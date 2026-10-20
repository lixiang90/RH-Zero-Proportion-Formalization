"""Read-only SDK/source resource analysis, with no Lean or author-script execution."""
from pathlib import Path
import hashlib
import json
import os
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SOURCE = ROOT / "research-goal-20261020-w9a2-delivery/draft-v7/Solution.lean"
SDK = Path("C:/Users/A/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/src/lean/Lean")
INPUTS = {}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read(path):
    data = path.read_bytes()
    INPUTS[str(path)] = {"path": str(path), "bytes": len(data), "sha256": sha(data)}
    return data


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def mask_comments_strings(raw):
    """Byte-preserving lexical mask; nesting and escapes handled, no elaboration."""
    out = bytearray(raw)
    i = 0
    while i < len(raw):
        if raw[i:i+2] == b"--":
            j = raw.find(b"\n", i)
            j = len(raw) if j < 0 else j
        elif raw[i:i+2] == b"/-":
            j, depth = i + 2, 1
            while j < len(raw) and depth:
                if raw[j:j+2] == b"/-":
                    depth += 1; j += 2
                elif raw[j:j+2] == b"-/":
                    depth -= 1; j += 2
                else:
                    j += 1
            require(depth == 0, "Unterminated comment")
        elif raw[i:i+1] == b'"':
            j = i + 1
            while j < len(raw):
                if raw[j:j+1] == b"\\":
                    j += 2
                elif raw[j:j+1] == b'"':
                    j += 1; break
                else:
                    j += 1
        else:
            i += 1; continue
        for k in range(i, min(j, len(raw))):
            if raw[k] not in (10, 13):
                out[k] = 32
        i = j
    return bytes(out)


def write_new(name, value):
    data = (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()
    with (HERE / name).open("xb") as stream:
        stream.write(data); stream.flush(); os.fsync(stream.fileno())
    return {"path": name, "bytes": len(data), "sha256": sha(data)}


def main():
    require(not (HERE / "files.json").exists(), "Exclusive report already exists")
    raw = read(SOURCE)
    require(len(raw) == 1829242 and sha(raw) == "dae01f6844642d7f9ee8180616c1f57aefc18ab8616bc8a4a46a14bf8e9fefc6", "Frozen v7 mismatch")
    masked = mask_comments_strings(raw)
    decls = list(re.finditer(rb"(?m)^((?:(?:private|protected|noncomputable) )*)(def|theorem|lemma|opaque|abbrev|structure|inductive) ([^\s(:]+)", masked))
    commands = list(re.finditer(rb"(?m)^(?:(?:private|protected|noncomputable) )*(?:def|theorem|lemma|opaque|abbrev|structure|inductive|end|section|namespace|open|set_option|attribute|instance|syntax|macro)\b", masked))
    command_starts = [m.start() for m in commands]
    data_rows, all_plain, owners = [], [], []
    for index, match in enumerate(decls):
        start = match.start()
        end = next((pos for pos in command_starts if pos > start), len(raw))
        name, kind = match.group(3).decode(), match.group(2).decode()
        owners.append((start, end, kind, name, match.end()))
        if kind != "def" or b"noncomputable" in match.group(1):
            continue
        eq = masked.find(b":=", match.end(), end)
        if eq < 0:
            clause = re.search(rb"(?m)^[ \t]+\|", masked[match.end():end])
            body_start = match.end() + clause.start() if clause else match.end()
        else:
            body_start = eq + 2
        body = raw[body_start:end].rstrip()
        row = {"name": name, "line": raw.count(b"\n", 0, start)+1, "declaration_start_byte": start,
               "body_start_byte": body_start, "body_end_byte_exclusive": body_start+len(body),
               "body_bytes": len(body), "body_sha256": sha(body), "declared_plain_def": True}
        all_plain.append(row)
        # Fixed conservative syntactic data classification; function definitions remain in all_plain.
        rhs = masked[body_start:body_start+len(body)].lstrip()
        header = masked[match.end():body_start]
        no_named_arguments = not re.search(rb"[({][A-Za-z]", header.split(b":", 1)[0])
        if no_named_arguments and (rhs.startswith((b"[", b"(", b"0x", b"zfNat64", b"|")) or name == "qState"):
            data_rows.append(row)
    all_plain.sort(key=lambda x: (-x["body_bytes"], x["line"]))
    data_rows.sort(key=lambda x: (-x["body_bytes"], x["line"]))
    names = [f"PTT_{i}" for i in range(8)] + ["PTT", "PT"]
    closure = []
    all_occurrences = []
    for name in names:
        pattern = rb"(?<![A-Za-z0-9_])" + name.encode() + rb"(?![A-Za-z0-9_])"
        refs = []
        for match in re.finditer(pattern, masked):
            owner = next((o for o in owners if o[0] <= match.start() < o[1]), None)
            require(owner is not None, "Unowned PTT/PT reference")
            if owner[3] == name and match.start() < owner[4]:
                continue
            refs.append({"line": raw.count(b"\n", 0, match.start())+1, "owner_kind": owner[2], "owner": owner[3], "byte_offset": match.start()})
        definition = re.search(rb"(?m)^def " + name.encode() + rb"\b[^\r\n]*(?:\r\n|\n)", raw)
        require(definition is not None, "Expected one-line ordinary data declaration")
        closure.append({"name": name, "line": raw.count(b"\n", 0, definition.start())+1,
                        "raw_declaration_bytes": len(definition.group()), "references": refs,
                        "hex_literals": definition.group().count(b"0x"),
                        "PTr_nd_tokens": definition.group().count(b".nd "), "PTr_lf_tokens": definition.group().count(b".lf ")})
        all_occurrences.extend(refs)
    expected_def_edges = {(f"PTT_{i}", "PTT") for i in range(8)} | {("PTT", "PT")}
    actual_def_edges = {(row["name"], ref["owner"]) for row in closure for ref in row["references"] if ref["owner_kind"] == "def"}
    require(actual_def_edges == expected_def_edges, "Computable caller closure changed")
    require(all(ref["owner_kind"] in ("def", "theorem") for ref in all_occurrences), "Unexpected runtime caller")
    options = [{"line": raw.count(b"\n", 0, m.start())+1, "value": m.group(1).decode()} for m in re.finditer(rb"(?m)^set_option Elab\.async (\w+)", masked)]
    require(options and all(row["value"] == "false" for row in options), "Unexpected async option")
    require(masked.find(b"section", masked.find(b"set_option Elab.async false")) > masked.find(b"set_option Elab.async false"), "Global async placement changed")
    sdk_files = ["CoreM.lean", "Shell.lean", "AddDecl.lean", "Elab/Command.lean", "Elab/Frontend.lean", "Elab/MutualDef.lean",
                 "Elab/PreDefinition/Basic.lean", "Elab/Tactic/Decide.lean", "Language/Lean.lean", "Compiler/LCNF/Main.lean",
                 "Compiler/LCNF/CompilerM.lean", "Compiler/LCNF/ConfigOptions.lean", "Compiler/LCNF/ExtractClosed.lean",
                 "Compiler/LCNF/Passes.lean", "Compiler/LCNF/ToLCNF.lean", "Compiler/LCNF/EmitC.lean",
                 "Elab/InfoTree/Types.lean", "Elab/InfoTree/Main.lean", "Server/References.lean"]
    for relative in sdk_files:
        read(SDK / relative)
    read(ROOT / "research-goal-20261020-w9a2-v7-official-failure-v1/technical-log.dom.txt")
    read(Path("C:/Users/A/.codex/attachments/a72e94e6-4105-44c0-b52c-8deca1fa0c23/已粘贴的文本.txt"))
    read(ROOT / "tmp/w9a2-20261020/fullchain-v2/logs/ordinary-Solution.Candidate.terminal.json")
    table = {"scope": "Byte-level lexical scan of frozen v7; ordinary def is not a proof that native code generation succeeded. No Lean elaboration performed.",
             "body_span_convention": "After first :=, or first equation clause, through next unindented declaration/scope command; trailing ASCII whitespace stripped. Byte offsets refer to exact raw UTF8.",
             "data_classification": "Conservative syntactic data-like RHS and no named argument before type colon; full ordinary-def ranking included to expose classification limits.",
             "top_data_like_plain_defs": data_rows[:30], "top_all_plain_defs": all_plain[:30],
             "all_data_like_plain_defs": data_rows, "plain_def_count": len(all_plain), "data_like_plain_def_count": len(data_rows)}
    row_table = write_new("ordinary-data-definitions.json", table)
    row_closure = write_new("PTT-caller-closure.json", {"scope": "All unquoted/uncommented exact-token references in frozen v7, with declaration ownership; byte-preserving lexer, not Lean name resolution.",
                                                        "namespace": "AMW.Cert.PC9QB6MData", "declarations": closure,
                                                        "all_computable_caller_edges": sorted([list(e) for e in actual_def_edges]),
                                                        "declared_total_bytes": sum(r["raw_declaration_bytes"] for r in closure),
                                                        "hex_literal_count": sum(r["hex_literals"] for r in closure),
                                                        "PTr_leaf_tokens": sum(r["PTr_lf_tokens"] for r in closure),
                                                        "PTr_node_tokens": sum(r["PTr_nd_tokens"] for r in closure)})
    for row in INPUTS.values():
        data = Path(row["path"]).read_bytes()
        require(sha(data) == row["sha256"] and len(data) == row["bytes"], "Frozen input changed")
    report = {"schema": "w9a2-v7-resource-static-formal-v1", "scope": "Static source, same-pin SDK and existing logs only; zero compiler/export/kernel/solver/network execution, zero frozen-source changes; counter untouched.",
      "v7_source_sha256": sha(raw), "v7_source_bytes": len(raw),
      "actual_failure": {"official_build_seconds": 1014, "Lean_exit_code": 137, "build_and_bash_exit_code": 1,
                         "type_error_proven": False, "OOM_proven": False, "warning_location_not_failure_location": True,
                         "limit": "SIGKILL-style exit is compatible with resource termination; no cgroup OOM/peakRSS receipt is present in these logs. No declaration-level timing is available."},
      "async": {"source_settings": options, "global_setting_before_first_section": True,
                "finding": "Ordinary theorem elaboration, kernel addDecl and compiler calls are synchronous under the already-effective false option. Adding the same option is a no-op.",
                "SDK": ["Elab/MutualDef.lean1236-1243", "AddDecl.lean169-181", "CoreM.lean730-750", "Elab/Command.lean362-368"],
                "not_claimed": "This does not make all frontend/reporting/import work single-threaded. Shell taskpool defaults to reported hardware concurrency (Shell219-237); -j1 is a separate runtime setting with unmeasured benefit.",
                "compiler_parallelism": "CompilerM559 and ElimDeadBranches297 explicitly use sync caches because compilation is non-parallel."},
      "retention": {"cmdline_snapshots": "Frontend288-292 defaults internal.cmdlineSnapshots=true. Language/Lean648-652 clears old command syntax/parser state;686-689 retains environment but discards other reported metadata. Setting false is not a justified memory reduction.",
                    "compiler_state": "LCNF Passes56-83 and116/139/158 save base/mono/impure representations; these are additional retained data beyond kernel expressions. No measured allocation attribution.",
                    "C_emission": "Shell552-568 runs frontend before optional C generation. emitC obtains a complete String then writes data.toUTF8; extra native-emission memory is plausible, not confirmed to be reached in the killed run."},
      "local_vs_official": {"local_v6": "-j1 -M13500 --tstack=262144 -DElab.async=false -o Candidate.olean; no -i/-c/--json",
                            "actual_official_v7": "-o Candidate.olean -i Candidate.ilean -c Candidate.c --setup Candidate.setup.json --json; no explicit -j/-M in captured argv",
                            "scope": "Local ordinary success is not evidence that the official C/ilean emission and resource limit passed. Ordinary -o still performs per-def IR generation; only its final C/ilean output path is absent."},
      "ilean_and_InfoTree": {"generation": "Language/Lean524-525 unconditionally enables InfoState;697-713 saves each command's InfoTree. This also occurs without -i. The source option Elab.async=false does not disable it.",
                "additional_i_path": "Frontend387-398 additionally gathers trees from snapshots, calls findModuleRefs and toLspModuleRefs, builds Ilean data and compact JSON, and writes the requested file. It runs after olean serialization381-385 and before returning the environment to Shell for C emission.",
                "retention": "Frontend409 explicitly says the snapshot graph and referenced data are not freed this close to exit. Thus the graph may coexist with final C String/toUTF8 allocation; this is not peak-memory measurement or proof the killed process reached that stage.",
                "user_option": "No registered SDK user option was found that disables InfoTree collection. InfoState.enabled is a field(Types313), and enableInfoTree/withEnableInfoTree(Main408-417) are elaborator APIs. trace.Elab.info only controls formatting/reporting, not collection. A new custom elaborator state mutation would be a separate, unreviewed change and is not proposed.",
                "candidate_proposal_limit": "Explicit noncomputable PTT annotations suppress executable compiler work but do not remove literal/proof-context InfoTrees or alter the official -i requirement."},
      "minimal_source_proposal": {"status": "STATIC_ONLY_NOT_APPLIED", "namespace": "AMW.Cert.PC9QB6MData", "names": names,
               "change": "Prefix only these ten existing def declarations with noncomputable, preserving all types/bodies/data/theorems and previous v7 changes.", "additional_source_bytes": 140,
               "data_size": "Ten declarations total160807 raw bytes;3483 hex literals,238 PTr leaves and237 PTr nodes by source-token count.",
               "complete_native_caller_boundary": "PTT_i -> PTT -> PT. All other references are theorem statements/proofs: PTT_i_ok, PTT_ok, ptS, rcOf/rcOfC. No unmarked computable caller is found.",
               "runtime_uses": "Tables are unfolded in theorem typechecking and the48 decide+kernel root reductions. Noncomputable tags preserve transparent kernel bodies and do not prevent reduction. The source's only macro executes ZeroForgePackedNat.decode64/digit64, which do not reference these tables and remain unchanged/executable.",
               "norm_num_boundary": "No candidate #eval, native_decide/+native, evalExpr/evalConst or metaprogram calls these ten declarations. Their occurrences are the recorded data-definition dependencies and theorem terms. Ordinary decide uses Meta WHNF or kernel reduction (Decide70-118), not native table evaluation; norm_num proof elaboration may still unfold kernel expressions, which remain present.",
               "implicit_compile_errors": "Explicitly tagging PTT and PT as well as8 children avoids attempts to compile callers with noncomputable dependencies. Basic134-140/217-223 skips codegen for marked declarations; ToLCNF440-450 documents the otherwise-rejected compiled reference. No additional source computable caller lies outside this closure.",
               "logical_preservation_basis": "Basic186-191 creates the same kernel defnDecl name/type/value/reducibility/safety; modifier only tags environment and controls compile call. No axiom/opaque/native checker change.",
               "remaining_cost": "Literal parsing, kernel expressions, all48 walks and table soundness proofs remain. Other plain-data and function definitions still generate IR/C. No guarantee this140B change materially lowers peak or fixes exit137."},
      "extract_closed_option": {"possible_change": "set_option compiler.extract_closed false", "SDK": "ConfigOptions38-41/73-76/93; ExtractClosed244-260; Passes139-141",
                                "effect": "Disables mono-phase extraction/caching of closed subterms into additional _closed declarations. It does not disable general codegen, base/mono/impure saves, kernel checking, ilean collection or final C output.",
                                "tradeoff": "Might reduce auxiliary declarations and closure-cache storage, but may duplicate constructor work or enlarge emitted bodies/runtime work. No memory/time measurement; not recommended as an additional uncontrolled change alongside the fixed ten-definition proposal."},
      "other_option_rejection": "compiler.postponeCompile branches are gated by env.header.isModule(Main142/169); this candidate is legacy source, so this is not a supported way to suppress its compilation.",
      "next_gate_scope": "Root may separately authorize one new-source resource compiler gate with the official -o/-i/-c/--setup/--json shape, record actual exit and peakRSS/time. No such execution or source derivation is authorized/performed by this report.",
      "input_hashes_before_after_identical": True, "inputs": list(INPUTS.values())}
    row_report = write_new("report.json", report)
    script = Path(__file__).read_bytes()
    files = [row_report, row_table, row_closure, {"path": "analyze.py", "bytes": len(script), "sha256": sha(script)}]
    row_manifest = write_new("files.json", {"schema": "static-resource-evidence-files-v1", "files": files, "proof_execution_count": 0})
    print(json.dumps({"source_sha256": sha(raw), "manifest_sha256": row_manifest["sha256"], "report_sha256": row_report["sha256"], "proposal_definitions": len(names), "inputs": len(INPUTS), "proof_execution_count": 0}))


if __name__ == "__main__":
    main()
