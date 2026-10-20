"""Static cache receipt/source comparison only; no Lean or olean data read."""
from pathlib import Path
import hashlib
import json
import os
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
inputs = {}
sha = lambda raw: hashlib.sha256(raw).hexdigest()
def read(path):
    raw = path.read_bytes(); inputs[path] = raw; return raw
def js(path):
    return json.loads(read(path))
def require(ok, message):
    if not ok: raise RuntimeError(message)
def new(name, value):
    raw = value if isinstance(value, bytes) else (json.dumps(value, ensure_ascii=False, indent=2)+"\n").encode()
    with (HERE / name).open("xb") as stream:
        stream.write(raw); stream.flush(); os.fsync(stream.fileno())

gate_path = ROOT / "research-goal-20261016/gates/w9a2-ordinary-v5-20261020.json"
gate = js(gate_path)
core_receipt = js(ROOT / "research-goal-20261020-w9a2-ordinary-v1-terminal/StructuralW9A220261020_Core.receipt.json")
core_command = js(ROOT / "research-goal-20261020-w9a2-ordinary-v1-terminal/StructuralW9A220261020_Core.command.json")
prefix_receipt = js(ROOT / "research-goal-20261020-w9a2-ordinary-v0-terminal/StructuralW9A220261020_Prefix.receipt.json")
read(ROOT / "research-goal-20261020-w9a2-ordinary-v1-terminal/StructuralW9A220261020_Core.log")
canonical_path = ROOT / "research-goal-20261020-w9a2-core-repair-v1/canonical-full/StructuralW9A220261020/Core.lean"
split_path = ROOT / "research-goal-20261020-w9a2-core-repair-v1/development-split/StructuralW9A220261020/Core.lean"
prefix_path = ROOT / "research-goal-20261020-w9a2-formal-static-review/development-split/StructuralW9A220261020/Prefix.lean"
canonical, split, prefix = read(canonical_path), read(split_path), read(prefix_path)
current_path = ROOT / "research-goal-20261021-w9a2-delivery/draft-v9/Solution.lean"
current = read(current_path)
require(sha(canonical) == "c2af225175f9a5ab14d2ba2612714a21e0613f66107a1d75b9d47bf1c77ba02a", "Wrong canonical Core")
require(sha(split) == core_receipt["source_sha256"] == "26e23c7fc4fbae33bdfff446901eaeb0f22f0f08fe13fa4e326541565a25279f", "Wrong compiled split source")
require(sha(prefix) == prefix_receipt["source_sha256"] == "bfd774658f3f855596a5453f86f4d98fbc884ca651b3e595d68f70b9553f5b3c", "Wrong Prefix source")
require(core_receipt["exit_code"] == prefix_receipt["exit_code"] == 0, "Missing actual ordinary PASS")
require(sha(current) == "7552bbb829b86986798b58cf40caf998ea8c51ab19201998b533dae4b9518c99", "Wrong v9")
marker = b"-- SWAP BEGIN certificate:"
require(canonical[canonical.index(marker):] == split[split.index(marker):], "Split suffix differs from canonical")
begin = b"/- BEGIN FLATTENED MODULE StructuralW9A220261020.Core -/\n"
end = b"\n/- BEGIN FLATTENED MODULE StructuralW9A220261020.Graph -/\n"
start = current.index(begin) + len(begin)
stop = current.index(end, start)
framed = current[start:stop]
require(framed.endswith(b"\n"), "Missing one flatten framing LF")
current_core = framed[:-1]
def normalize(raw):
    lines = raw.splitlines(keepends=True)
    kept = [line for line in lines if not line.startswith((b"import ", b"#print axioms "))]
    body = b"".join(kept)
    return re.sub(rb"(?m)^((?:(?:private|protected) )*)noncomputable (?=(?:def|abbrev|instance)\b)", rb"\1", body)
old_normalized, new_normalized = normalize(canonical), normalize(current_core)
require(old_normalized == new_normalized, "Core differs beyond imports/prints/explicit declaration noncomp")
apis = {}
for name in ("QuantGoal", "Covered", "CutsOk", "walkCutR", "rcOfC", "WD10", "rc10"):
    pattern = rb"(?m)^(?:(?:noncomputable|private|protected) )*(?:def|abbrev|theorem) " + name.encode() + rb"\b[^\n]*"
    match = re.search(pattern, current_core)
    require(match is not None, "Missing pilot API " + name)
    apis[name] = {"line_in_v9": current.count(b"\n", 0, start+match.start())+1, "header": match.group().decode()[:600]}
require(apis["WD10"]["header"].endswith("rdw WL10"), "Wrong WD10")
require("270277" in apis["rc10"]["header"] and "RC 0 0 1 0 1 0 0 0" in apis["rc10"]["header"], "Wrong root10 target")
reused = [row for row in gate["reused_oleans"] if row["module_path"] in {"StructuralW9A220261020/Core.olean", "StructuralW9A220261020/Prefix.olean"}]
require(len(reused) == 2, "Missing reused dependency pins")
artifacts = []
for row in reused:
    path = ROOT / row["path"]
    stat = path.stat()
    artifacts.append({**row, "absolute_path": str(path), "current_stat_bytes": stat.st_size,
                      "current_olean_bytes_read_or_hashed": False, "identity_scope": "SHA is original PASS receipt+ordinary-v5 reuse gate, not recomputed by this static review"})
for name in ("Core.olean", "Prefix.olean"):
    path = ROOT / "tmp/w9a2-20261020/candidate-ordinary-v5/lib/StructuralW9A220261020" / name
    stat = path.stat()
    artifacts.append({"absolute_path": str(path), "current_stat_bytes": stat.st_size,
                      "role": "ordinary-v5 copied overlay file; original source artifact pin remains above", "current_olean_bytes_read_or_hashed": False})
for path, raw in inputs.items(): require(path.read_bytes() == raw, "Source/metadata input changed")
report = {"schema": "cached-strengthened-Core-pilot-static-v1", "result": "STATICALLY_FEASIBLE_AS_EXPLICIT_TRUSTED_DEPENDENCY_NOT_EXECUTED",
    "exact_import": "import StructuralW9A220261020.Core",
    "module_names": ["StructuralW9A220261020.Prefix", "StructuralW9A220261020.Core"],
    "old_Core_PASS": core_receipt, "old_Prefix_PASS": prefix_receipt,
    "ordinary_v5_reuse_gate": {"path": str(gate_path), "sha256": sha(inputs[gate_path]), "declared_sha256_in_started": "5a928e8066bd0c8a1bb3cd9e28028b9c995dd40728eed3e72612f9ca8f086d0e"},
    "retained_artifact_descriptors": artifacts,
    "source_identity": {"canonical_full_sha256": sha(canonical), "compiled_split_source_sha256": sha(split), "Prefix_source_sha256": sha(prefix),
                        "canonical_suffix_after_SWAP_exactly_split_suffix": True,
                        "v9_flat_Core_extraction": {"start_byte": start, "end_before_one_framing_LF": stop-1, "bytes": len(current_core)},
                        "comparison_rule": "Remove only import lines and standalone#print axioms lines, and explicit noncomputable before def/abbrev/instance keywords; remove exactly one flat framing LF. All remaining original body/statement/data/comment/scope bytes equal.",
                        "normalized_Core_bytes": len(old_normalized), "normalized_Core_sha256": sha(old_normalized), "current_math_body_matches_old_strengthened_Core": True,
                        "not_same_full_source_SHA_or_compilation_metadata": True},
    "pilot_API": apis,
    "pilot_required_goal_scope": {"namespace_data": "AMW.Cert.PC9QB6MData", "namespace_generic": "AMW.Cert.PC9QB6M", "root": "RC 0 0 1 0 1 0 0 0", "word_stream": "WD10 = rdw WL10", "end_cursor": 270277,
                                 "desired_parent_equation": "U (walkCutR TOP BK TOPD BKD PT REG WD10 cuts 128 1) (ofCl (RC 0 0 1 0 1 0 0 0) 0) = 270277",
                                 "desired_final_proposition": "Covered (RC 0 0 1 0 1 0 0 0)",
                                 "new_proof_obligations": "Concrete child raw walks/current exact cut states and cursors, CutsOk cuts and the parent cut equation; then rcOfC with270277 !=0. No old f82a cut data/end235228 may be imported as current evidence."},
    "no_tautological_pilot": "Imported Core already contains rc10 and run/run8. A new pilot must not simply exact those existing coverage proofs or derive child coverage from the old whole proof. Use the existing generic cut soundness theorems and exact data, then independently check the new child equations and parent factorization. A future dependency audit must distinguish this new proof from reuse of old rc10/run.",
    "trusted_dependency_scope": "Reuse exact already checked module artifacts and matching SDK/package versions from the frozen ordinary-v5 gate/known trusted dependencies. Import loads their existing checked declarations; it is not a new elaboration or independent replay of all old proofs. Current2 olean SHA checks and setup belong to a later explicit root-owned gate; none was performed here.",
    "resource_scope": "A new pilot can avoid rebuilding old Core and aim only at fresh child/cut proofs. Imports still load Prefix/Core and matching Mathlib/Zeta dependencies; import memory and pilot reduction costs are unmeasured. Even a successful pilot would not establish whole single-file v9/resource/official3200 or independent-kernel acceptance.",
    "no_execution": {"Lean": 0, "compiler": 0, "kernel": 0, "exporter": 0, "decoder": 0, "new_source_generation": 0, "library_tree_rehash": 0, "olean_full_hash": 0, "Git_or_counter_changes": 0},
    "inputs_before_after_equal": [{"path": str(path), "bytes": len(raw), "sha256": sha(raw)} for path, raw in inputs.items()]}
new("review.json", report)
new("README.zh.md", ("可静态支持新的pilot显式import StructuralW9A220261020.Core。Core真实ordinary PASS来自v1：source26e23…、olean4e24…/45826856B；Prefix真实PASS来自v0：sourcebfd774…、oleane9bbc…/39261904B。ordinary-v5 gate5a928…明确复用这两份原artifact；v5/lib也有同大小副本。本审只stat olean，不重hash或读其内容，不扫library tree。\n\n编译的split Core后缀与canonical full c2af…在SWAP处后逐byte相同。对canonical和v9 flattened Core，仅除import、独立#print、def/abbrev/instance显式noncomp及一个flat framing LF，其余全部原始bytes精确相同。这支持旧缓存含同版强化QuantGoal、Covered及WD10，不把v9 metadata与旧module假称同SHA。\n\n新pilot应针对AMW.Cert.PC9QB6MData.WD10、RC(0,0,1,0,1,0,0,0)、128 fuel/起点1/end270277，用当前cut states的两child raw walk证明CutsOk及父walkCutR等式，再rcOfC推出同Covered。旧Core已有rc10/run；不能直接拿它们当新的切分证明。旧f82a cuts/end235228不匹配，不能移植。\n\n没有编译、Lean、kernel、decoder或新Lean源；当前artifact bytes身份仅引用旧PASS/reuse gate，后续真实root门须自行fresh核2artifact及匹配依赖。pilot成功也只证明新切分在显式trusted模块下成立，不是最终单文件、低峰资源或官网全链通过。\n").encode())
members=[]
for path in sorted(HERE.iterdir()):
    if path.is_file() and path.name != "files.json":
        raw=path.read_bytes(); members.append({"path":path.name,"bytes":len(raw),"sha256":sha(raw)})
new("files.json", {"schema":"cached-Core-pilot-static-files-v1","files":members})
print(json.dumps({"manifest_sha256":sha((HERE/"files.json").read_bytes()),"review_sha256":sha((HERE/"review.json").read_bytes()),"normalized_Core_bytes":len(old_normalized),"no_olean_data_read":True}))
