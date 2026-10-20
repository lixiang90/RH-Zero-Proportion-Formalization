"""Static source offsets and SDK evidence only; never creates modified Lean source."""
from pathlib import Path
from collections import Counter
import hashlib
import json
import os
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SOURCE = ROOT / "research-goal-20261020-w9a2-delivery/draft-v8/Solution.lean"
SDK = Path("C:/Users/A/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/src/lean/Lean")
sha = lambda value: hashlib.sha256(value).hexdigest()
inputs = {}

def read(path):
    value = path.read_bytes(); inputs[path] = value; return value

def encode(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()

def new(name, value):
    raw = encode(value) if not isinstance(value, bytes) else value
    with (HERE / name).open("xb") as stream:
        stream.write(raw); stream.flush(); os.fsync(stream.fileno())

def mask(raw):
    out = bytearray(raw); i = 0
    while i < len(raw):
        if raw[i:i+2] == b"--":
            j = raw.find(b"\n", i); j = len(raw) if j < 0 else j
        elif raw[i:i+2] == b"/-":
            j, depth = i + 2, 1
            while j < len(raw) and depth:
                if raw[j:j+2] == b"/-": depth += 1; j += 2
                elif raw[j:j+2] == b"-/": depth -= 1; j += 2
                else: j += 1
            if depth: raise RuntimeError("Unclosed nested comment")
        elif raw[i] == 34:
            j = i + 1
            while j < len(raw):
                if raw[j] == 92: j += 2
                elif raw[j] == 34: j += 1; break
                else: j += 1
        else: i += 1; continue
        for k in range(i, min(j, len(raw))):
            if raw[k] not in (10, 13): out[k] = 32
        i = j
    return bytes(out)

raw = read(SOURCE)
if len(raw) != 1829382 or sha(raw) != "5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b":
    raise RuntimeError("Wrong frozen v8")
inventory_path = HERE / "source-inventory.json"
inventory_raw = read(inventory_path)
if sha(inventory_raw) != "da9b9258508f7d6f83facfc70b127231f480cecefe4e9a3b651760bce5aa88d0":
    raise RuntimeError("Inventory changed")
inventory = json.loads(inventory_raw)
clean = mask(raw)
rows = inventory["ordinary_def_abbrev_opaque_instance_candidates_excluding_decoder"]
offsets = []
for row in rows:
    start = row["byte_offset"]; end = raw.find(b"\n", start)
    if end < 0: end = len(raw)
    header = clean[start:end]
    match = re.match(rb"(?P<mods>(?:(?:private|protected|local|scoped)\s+)*)(?P<kind>def|abbrev|instance)\b", header)
    if match is None or match["kind"].decode() != row["kind"]:
        raise RuntimeError("Candidate keyword offset cannot be independently matched")
    offset = start + match.start("kind")
    if raw[offset:offset+len(match["kind"])] != match["kind"]:
        raise RuntimeError("Not raw UTF8 keyword offset")
    offsets.append({"UTF8_keyword_byte_offset_0based": offset, "line_1based": row["line"], "kind": row["kind"],
                    "name_as_written": row["name"], "original_modifiers": row["modifiers"],
                    "original_header_preview": raw[start:end].decode()[:220],
                    "original_header_sha256": sha(raw[start:end]), "proposed_insertion": "noncomputable ", "insertion_bytes": 14})
if len(offsets) != 2267 or len({row["UTF8_keyword_byte_offset_0based"] for row in offsets}) != 2267:
    raise RuntimeError("Unexpected candidate count")
if Counter(row["kind"] for row in offsets) != Counter({"def": 2257, "abbrev": 5, "instance": 5}):
    raise RuntimeError("Unexpected candidate kinds")
prefix_end = raw.find(b"set_option Elab.async false")
if prefix_end < 0 or any(row["UTF8_keyword_byte_offset_0based"] < prefix_end for row in offsets):
    raise RuntimeError("Macro prefix is not excluded")
if any(row["name_as_written"] in {"digit64", "decode64"} for row in offsets):
    raise RuntimeError("Decoder accidentally selected")
sdk_files = ["Elab/PreDefinition/Basic.lean", "Elab/PreDefinition/Main.lean", "Elab/MutualDef.lean",
             "Parser/Command.lean", "Compiler/LCNF/ToLCNF.lean", "Elab/Util.lean",
             "KeyedDeclsAttribute.lean", "Environment.lean", "Elab/Tactic/Decide.lean",
             "Meta/SynthInstance.lean", "Meta/Tactic/Simp/Attr.lean", "Elab/BuiltinCommand.lean",
             "Meta/Structure.lean"]
for name in sdk_files: read(SDK / name)
special_tokens = ["meta", "partial", "unsafe", "nonrec", "run_meta", "run_elab", "by_elab", "declare_syntax_cat", "notation", "infix", "infixl", "infixr", "prefix", "postfix", "simproc", "simproc_decl", "dsimproc", "register_option", "register_builtin_option", "extern", "implemented_by", "csimp", "compiler_simp"]
special = {}
for token in special_tokens:
    special[token] = [{"line": raw.count(b"\n", 0, match.start())+1, "UTF8_byte_offset": match.start()} for match in re.finditer(rb"(?<![A-Za-z0-9_'])" + token.encode() + rb"(?![A-Za-z0-9_'])", clean)]
rec_helpers = {"let_rec_tokens": [{"line": raw.count(b"\n", 0, match.start())+1, "UTF8_byte_offset": match.start()} for match in re.finditer(rb"\blet\s+rec\b", clean)], "where_tokens": [{"line": raw.count(b"\n", 0, match.start())+1, "UTF8_byte_offset": match.start()} for match in re.finditer(rb"\bwhere\b", clean)]}
preserved = {"macro_prefix_byte_interval": [0, prefix_end], "macro_prefix_bytes": prefix_end, "macro_prefix_sha256": sha(raw[:prefix_end]),
             "source_declared_runtime_functions": [{"name": "ZeroForgePackedNat.digit64", "source_line": 73, "private": True}, {"name": "ZeroForgePackedNat.decode64", "source_line": 91, "private": False}],
             "macro_command": {"name": "zfNat64", "source_line": 120},
             "source_runtime_edges": [["zfNat64 macro expansion", "ZeroForgePackedNat.decode64"], ["ZeroForgePackedNat.decode64", "ZeroForgePackedNat.digit64"]],
             "local_generated_runtime_to_preserve": "All syntax-parser, macro expander, match/lambda/loop/helper declarations generated from the unchanged prefix. Exact internal names/count require elaboration and are not claimed here.",
             "imported_runtime": "Lean parser/MacroM/Syntax, Nat/String/ByteArray/Except/ForIn and their imported generic instances/native primitives. These are imported SDK code, not candidate declarations selected for annotation.",
             "packing_calls": len(inventory["decoder_and_packing_refs"]["zfNat64"]),
             "other_classes_excluded_from_modification": {"theorem": 1021, "lemma": 195, "structure": 14, "inductive": 1, "existing_noncomputable_def": 21},
             "no_generated_Lean_source_produced": True}
new("candidate-keyword-offsets.json", {"scope": "Metadata-only proposal. Every offset is zero-based raw UTF8 byte position of the original def/abbrev/instance keyword; no modified proof file was generated.", "source_sha256": sha(raw), "count": len(offsets), "kind_counts": dict(Counter(row["kind"] for row in offsets)), "proposed_total_inserted_bytes": len(offsets)*14, "hypothetical_source_bytes": len(raw)+len(offsets)*14, "modifiers_order": "Insert immediately before keyword, after existing private/protected. Do not prefix all commands.", "candidates": offsets})
new("preserved-runtime-closure.json", preserved)
report = {
    "schema": "w9a2-whole-file-native-suppression-static-formal-v1",
    "status": "STATIC_CONDITIONAL_PROPOSAL_ONLY_NOT_IMPLEMENTED_OR_EXECUTED",
    "scope": "Read frozen1.8MB v8 and necessary same-pin SDK source only. No source edit, generated Lean variant, Lean/parser/import/AST/compiler/kernel/export/solver/API/probe/network/large-export/runtime-tree scan/state/counter/Git change.",
    "source": inventory["source"], "Lean_commit": "d8b18978322de05a8f3dba51ef03cf5461676c17",
    "lexical_inventory": {"all_explicit_declarations": sum(inventory["declaration_counts"].values()), "kind_counts": inventory["declaration_counts"], "existing_explicit_noncomputable_defs": 21, "candidate_kind_counts": {"def": 2257, "abbrev": 5, "instance": 5}, "candidate_total": 2267, "source_level_keyword_offsets": "candidate-keyword-offsets.json", "hypothetical_bytes_if_only14B_insertions": 1861120},
    "real_runtime_entries": preserved,
    "metadata_only_commands_and_attributes": {"simp_attributes": 13, "simp_owners": "All13 explicitly annotate theorem/lemma proof declarations, not Simproc/NormNum extension functions", "irreducible_attribute": {"line": 7704, "names": ["CellN.okC", "CellN.NLOZ", "CellN.DHIZ", "CellN.WZ", "CellN.okD", "CellN.W1LO", "CellN.W1HI", "CellN.convOk"], "role": "Changes Meta reducibility/unfolding status, not executable registration"}, "export_alias_command": {"line": 13533, "source": "export Meshuggah (sincN phiC hat)", "SDK": "Elab/BuiltinCommand.lean298–310 only resolves names and addAlias; no new definition or compile"}, "hash_commands": inventory["hash_commands"], "additional_special_token_hits": special},
    "instance_and_tactic_boundary": {"anonymous_source_instances": [row for row in inventory["all_explicit_declarations"] if row["kind"] == "instance"], "instance_types": ["Decidable(PRok Q PR)", "Decidable(TSok Q PR TS)", "Decidable(SLok Q PR SL)", "Decidable(Edge u v)", "Decidable(Conflict u v)"], "meaning": "These are data-level Decidable instances (Type), not propositions or user-defined meta callbacks. SDK synthesis constructs instance Expr terms; decide+kernel checks via mkAuxLemma/kernel. Explicit noncomputable is compatible with logical reduction/instance lookup, but prevents native use of their executable implementations.", "imported_tactic_runtime": "simp/norm_num/ring/linarith and command elaborators still execute imported meta code. No candidate norm_num/simproc/extern/implemented_by/csimp attribute, initializer, elab, run_cmd/run_tac/#eval/native_decide is present. Absence of a local executable extension narrows the local callback closure; this static inventory is not an exhaustive proof about arbitrary imported meta implementations or all elaboration-generated declarations."},
    "SDK_semantics": [
        {"path": "Elab/PreDefinition/Basic.lean", "lines": [134, 140, 186, 223], "fact": "shouldGenCodeFor requires non-theorem and no explicit noncomputable. Definition values/types/safety and ordinary/abbrev reducibility hints are constructed before tag/codegen selection. Instance kind chooses theorem if its type is Prop, otherwise definition. noncomputable section alone only changes compile diagnostic handling."},
        {"path": "Elab/PreDefinition/Main.lean", "lines": [303, 310], "fact": "A nonrecursive noncomputable predefinition uses addNonRec(cleanupValue:=true), while ordinary uses addAndCompileNonRec with the same cleanup argument; skipping codegen is deliberate, not replacing the logical value."},
        {"path": "Elab/MutualDef.lean", "lines": [96, 99, 1092, 1101, 1214, 1233], "fact": "Noncomputable theorem and noncomputable partial are rejected. let-rec helpers inherit a main declaration's noncomputable modifier; tags are added early. Non-Prop instances keep instanceReducible default. Source has no explicit partial/unsafe/meta declarations; generated recursion artifacts remain an implementation boundary."},
        {"path": "Parser/Command.lean", "lines": [100, 121], "fact": "Visibility/protected precede noncomputable; unsafe/partial follow. Insert before the keyword only when original modifiers match the inventory; do not prepend to arbitrary commands."},
        {"path": "Compiler/LCNF/ToLCNF.lean", "lines": [440, 452], "fact": "A compiled caller of a noncomputable declaration or its noncomputable unsafe_rec implementation is rejected unless exempt extern/implemented_by primitives. This is why preserving the whole executable decoder closure matters; annotating the decoder is not safe."},
        {"path": "Meta/Structure.lean", "lines": [104, 123], "fact": "Projections are generated defnDecl constants and registered as projection functions. Compiler has special support and they need not be compiled by this generator. This does not eliminate all other generated native artifacts."},
        {"path": "KeyedDeclsAttribute.lean / Elab/Util.lean / Environment.lean", "lines": [166, 158, 165, 2518, 2539], "fact": "Registration obtains executable callbacks via evalConstCheck/evalConst; macro expansion invokes e.value stx. The unchanged source prefix's macro/decoder and all its generated implementations must stay executable."},
        {"path": "Meta/Tactic/Simp/Attr.lean", "lines": [42, 59], "fact": "Simp checks if a declaration is a Simproc; otherwise proof types add a simp theorem or definitions add unfolding entries. These13 local simp attributes target proof declarations and do not register candidate-native procedures."}
    ],
    "why_existing8_plus10_is_not_whole_native_boundary": "Only18 chosen definitions were newly annotated before v8, in addition to3 older explicit noncomputable definitions.2257 other explicit ordinary defs,5 abbrevs and5 Decidable instances remain eligible for codegen attempts under SDK rules, subject to type erasure/noncomputability/failures. This includes small helpers, balanced selectors, integer arithmetic and the many literal data definitions, not only the ten PTT nodes. Conversely source-level types/constructors/recursors/CtorIdx and macro-generated executable code have separate generators. Candidate counts are source opportunities, not a measurement that every one produced a native function or that it dominates memory.",
    "candidate_assessment": "Semantically plausible, substantial fixed-scope native-compilation suppression proposal: annotate precisely the2267 listed ordinary def/abbrev/Decidable instance keywords, preserve the entire macro prefix and all other command/body/data bytes. Keep1216 theorem/lemma proofs and14structures/1inductive unchanged. Kernel definitions remain for ordinary reduction; this does not remove finite checks or replace proof bodies. It is not authorized or implemented by this report.",
    "unproven_boundaries": ["Exact internal generated declaration names/counts, implicit matcher/termination/unsafe_rec/projection/constructor/index helpers and their codegen behavior for this whole file without elaboration", "No claim all generated native work becomes zero; structure/inductive types/constructors reject noncomputable modifiers and generators such as CtorIdx may compile independently", "Imported tactics may inspect/reduce candidate expressions; no arbitrary imported-meta callback audit is performed. No local executable plugin beyond the preserved macro was identified", "Early noncomputable tags can affect compiler validation/realization paths and generated auxiliary inventory; all generated kernel declarations are not claimed byte-identical", "No guarantee that a full modified source compiles, retains every generated-name behavior, lowers peak memory or fits official resources", "Kernel expression/data/InfoTree/import retention,48root reductions and official whole-pipeline obligations remain", "Anonymous instance elaborated names, private name encodings and full namespace/name resolution are not certified by the lexical inventory"],
    "generated_code_exclusion_rule": "Do not add modifiers to structure/inductive/type/constructor fields or theorem/lemma commands. Preserve generated artifacts of runtime macro prefix. Do not equate this source-keyword proposal with an automatically complete environment/codegen declaration inventory.",
    "recursion_tokens": rec_helpers,
    "stop_boundary": "No new source, generator execution, compile/import/AST/kernel or enabled gate. Root must separately review the fixed keyword proposal and decide any future implementation/validation; task completion does not authorize a new batch.",
    "inputs": [{"path": str(path), "bytes": len(value), "sha256": sha(value)} for path, value in inputs.items()]
}
for path, value in inputs.items():
    if path.read_bytes() != value: raise RuntimeError("Read-only input changed")
report["all_inputs_before_after_equal"] = True
new("report.json", report)
new("README.zh.md", ("# 整个固定v8的普通声明noncomputable：有限静态提案\n\n"
    "除宏decoder运行闭包外，候选是2257 def+5abbrev+5Decidable instance，共2267处；UTF-8 byte keyword offsets及原modifiers逐项见candidate-keyword-offsets.json。若只插14B，预计1861120B。本报告没有生成这份修改源。\n\n"
    "唯一source层执行入口是zfNat64宏；必须保留整个macro前缀及ZeroForgePackedNat.decode64→private digit64，连同其生成的parser/expander/matcher/lambda/loop实现。135个WL调用运行该宏，随后kernel只得到普通Nat numeral。无其它显式elab/run_cmd/run_tac/#eval/初始化/deriving/native_decide或本地可执行属性入口。13个simp属性都标proof，另有irreducible和只addAlias的export。\n\n"
    "新增18modifier加旧3个只覆盖21个显式def；其余2257显式普通def、5abbrev、5数据instance仍会经过各自代码生成/擦除/失败处理。故18处不能代表全native工作边界。反过来，14structure和1inductive的构造器/递归器/自动helper另有生成路径，不能直接加noncomputable；投影有special compiler support，CtorIdx等仍可能独立compile。不能承诺零生成代码。\n\n"
    "SDK明确noncomp保留普通definition type/value/hints，并跳过该路径compile；abbrev仍abbrev hints，Decidable instance仍可合成和kernel归约。let rec传播主modifier，非递归采用同cleanup。theorem/lemma本来不生成代码，加noncomp会被拒绝；也不能注释runtime decoder或把noncomp section当成全禁编译。\n\n"
    "这是条件可行、尚未实施的整文件普通声明codegen削减提案；不是语义或资源验收。精确生成名字/数量、所有imported meta实现及逐生成kernel声明身份无Lean时不能证明；未测哪些声明真生成native，更未测memory收益。数据、48根逻辑归约、环境/InfoTree/import成本仍在。没有改proof、运行Lean/parser/AST/import/compiler/kernel/export、重扫大input/closure、改变state/counter或Git。\n").encode())
members = []
for path in sorted(HERE.iterdir()):
    if path.is_file() and path.name != "files.json":
        value = path.read_bytes(); members.append({"path": path.name, "bytes": len(value), "sha256": sha(value)})
new("files.json", {"schema": "whole-file-runtime-closure-static-files-v1", "files": members})
print(json.dumps({"manifest_sha256": sha((HERE / "files.json").read_bytes()), "report_sha256": sha((HERE / "report.json").read_bytes()), "candidate_offsets_sha256": sha((HERE / "candidate-keyword-offsets.json").read_bytes()), "candidate_count": len(offsets), "members": len(members), "no_modified_source_generated": True}))
