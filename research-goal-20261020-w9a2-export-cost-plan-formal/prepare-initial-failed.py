"""Preparation only: read at most five export lines, never stream/hash an export."""
from pathlib import Path
import hashlib
import json
import os

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
JOB = ROOT / "tmp/w9a2-20261020/fullchain-v2"
ARCHIVE = ROOT / "research-goal-20261020-w9a2-fullchain-v2-terminal"
MAX_PREFIX_LINE = 262144
inputs = {}

def sha(value):
    return hashlib.sha256(value).hexdigest()

def read_small(path):
    value = path.read_bytes()
    if len(value) > 200000:
        raise RuntimeError("Unexpectedly large metadata/source input")
    inputs[path] = value
    return value

def js(path):
    return json.loads(read_small(path))

def new(path, value):
    with path.open("xb") as stream:
        stream.write(value); stream.flush(); os.fsync(stream.fileno())

def encode(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()

retained = js(ARCHIVE / "retained-binary-and-export-artifacts.json")
generation = js(ARCHIVE / "job/generation.json")
ordinary = js(ARCHIVE / "job/logs/ordinary-Solution.Candidate.terminal.json")
read_small(ARCHIVE / "files.json")
if generation["source_sha256"] != "a517df6aebde6d136f8b83e06c8be10b3413b8430390f52bd47f04e06f0dce26" or ordinary["exit_code"] != 0:
    raise RuntimeError("Wrong historical source/ordinary receipt")
exports = []
for name, wanted_size, wanted_sha in (("challenge", 349332110, "a292e2fc44e0b69bcfaad53175bbeb1cda71b14b1edaab4bb779160f949bc6d0"), ("solution", 677296932, "1cc0f929919e0d4f58d947223c75a82450df57da11a9fe43fd93a90d8c8433d7")):
    terminal_path = JOB / f"logs/{name}-native-export.terminal.json"
    terminal = js(terminal_path)
    archived = js(ARCHIVE / f"job/logs/{name}-native-export.terminal.json")
    path = JOB / f"{name}.ndjson"
    stat_before = path.stat()
    if terminal != archived or terminal["exit_code"] != 0 or terminal["output_bytes"] != wanted_size or terminal["output_sha256"] != wanted_sha or stat_before.st_size != wanted_size:
        raise RuntimeError("Export metadata differs")
    matching = [row for row in retained if row["path"] == path.relative_to(ROOT).as_posix()]
    if len(matching) != 1 or matching[0]["sha256"] != wanted_sha:
        raise RuntimeError("Retained descriptor differs")
    prefix = []
    with path.open("rb", buffering=0) as stream:
        for index in range(5):
            line = stream.readline(MAX_PREFIX_LINE + 1)
            if not line:
                break
            if len(line) > MAX_PREFIX_LINE or not line.endswith(b"\n"):
                raise RuntimeError("Prefix line too long; no further export bytes read")
            prefix.append(line)
    stat_after = path.stat()
    if (stat_before.st_size, stat_before.st_mtime_ns) != (stat_after.st_size, stat_after.st_mtime_ns):
        raise RuntimeError("Export metadata changed while reading prefix")
    prefix_raw = b"".join(prefix)
    parsed = [json.loads(line) for line in prefix]
    new(HERE / f"{name}-first-five-lines.ndjson", prefix_raw)
    exports.append({"role": name, "absolute_path": str(path), "current_stat_bytes": stat_after.st_size,
                    "historically_recorded_full_file_sha256": wanted_sha,
                    "full_file_sha256_recomputed_this_preparation": False,
                    "original_terminal": {"path": str(terminal_path), "bytes": len(inputs[terminal_path]), "sha256": sha(inputs[terminal_path]), "exit_code": terminal["exit_code"], "elapsed_seconds": terminal["elapsed_seconds"], "argv": terminal["argv"]},
                    "prefix_only": {"lines": len(prefix), "bytes": len(prefix_raw), "sha256": sha(prefix_raw), "decoded": parsed},
                    "stat_size_and_mtime_unchanged_while_prefix_read": True})
exporter_paths = [ROOT / "tmp/lean4export/Export.lean", ROOT / "tmp/lean4export/Main.lean", ROOT / "tmp/lean4export/Export/Parse.lean"]
expected = ["1c60d571dc24bfb99e7cbb218d8d489919bbc871238f6db9c76248521fbea998", "bd8e350903f1382b25fe767f9086dd9882000f01085f7046ea06545e7848842a", "1f943b5cc776eece6d528937b976509c8bd57d10bc69a39b1c119bfb6d664286"]
for path, expected_sha in zip(exporter_paths, expected):
    value = read_small(path)
    if sha(value) != expected_sha:
        raise RuntimeError("Exporter source pin differs")
read_small(ROOT / "research-goal-20261020-w9a2-verification-preparation-v1/run_verification.py")
metadata = exports[0]["prefix_only"]["decoded"][0]
if metadata != exports[1]["prefix_only"]["decoded"][0]:
    raise RuntimeError("Export metadata headers differ")
plan = {
    "schema": "w9a2-v6-export-structural-cost-plan-v1", "status": "PREPARATION_ONLY_NOT_EXECUTED",
    "scope": "One proposed inert NDJSON structural scan, no Lean/kernel/export/compiler/solver. Strictly only the historical solution export may be fully streamed; challenge is not fully read.",
    "input": {"path": str(JOB / "solution.ndjson"), "expected_bytes": 677296932, "expected_sha256": exports[1]["historically_recorded_full_file_sha256"], "historical_source_sha256": generation["source_sha256"], "historical_source_bytes": generation["source_bytes"]},
    "limits": {"complete_export_streams": 1, "input_to_stream": "solution.ndjson only, one forward pass; no seek/backtracking/retry", "wall_clock_seconds_including_setup_finalization": 120, "process_memory_cap_bytes": 268435456, "retained_name_table_cap_bytes": 33554432, "maximum_input_line_bytes": 1048576, "maximum_aggregate_output_bytes": 2097152, "maximum_ranked_declaration_rows": 100},
    "input_binding": "Stat size before/after; verify all677296932 bytes and SHA1cc0... while consuming that same one pass. Check header and node/reference ordering. Any mismatch, cap, malformed line, allocation failure or deadline produces incomplete/failed audit, no complete ranking and no automatic retry.",
    "algorithm": [
        "Pin small receipts/exporter source and the selected known-v6 source/namespace classification list; do not import author code. Start120s deadline before setup.",
        "Open only solution once, binary; read bounded lines and increment SHA256/byte offset from those exact bytes. Parse one JSON object at a time; discard it after updating bounded counters. Do not recreate Lean Expr values.",
        "Maintain compact bounded parent/index/name-component storage only for resolving declaration and const names. Stop failclosed if32MiB retained-name storage,1MiB line or256MiB whole-process budget would be exceeded; exact actual enforcement must be independently specified before any execution.",
        "Count record kinds and exact line bytes globally. For expressions count ie records by constructor, natVal decimal characters, strVal UTF8 bytes, const occurrences and ie maximum. Count declaration rows by kind and retain root ids type/value/recursor rhs without expanding them.",
        "Maintain a single current sequential segment from the byte immediately after the previous declaration record to the end of the current declaration record. At each declaration record emit/update top100 by segment bytes, expression count, natVal digits and declaration-line bytes; reset segment counters. Treat an inductive block as one record/group, not separate emitted constructor records.",
        "Label a declaration known-v6-local namespace/name match or origin_unresolved using an already reviewed explicit list, retaining private-name caveats. This is not an exact solution-minus-challenge set. No full challenge read is authorized by this plan.",
        "At EOF compare bytes/SHA with original receipt, stat metadata and limits; output bounded summary/top rows with completion/failure flags and self-contained metric definitions. Output total≤2MiB. Do not output or modify an export/proof/runtime input."
    ],
    "metric_definitions": {
        "declaration_record_bytes": "Exact UTF8 NDJSON line bytes for a def/thm/opaque/axiom/quot/inductive record, including LF. Type/value are expression indices, not serialized inline trees.",
        "sequential_segment_bytes": "Reproducible byte interval after prior declaration LF through current declaration LF; includes emitted names/levels/new expression nodes and current declaration row. It is first-emission serialization accounting, not ownership of every referenced node.",
        "segment_expression_records": "Number of emitted ie rows in that interval. Shared nodes already emitted earlier add zero here; nested dependency declarations reset boundaries and can receive serialization first encountered by a later root.",
        "natVal_decimal_characters": "Exact exported decimal digit length of literal natVal strings. This can expose packed integer magnitude/serialization cost; it does not measure original zfNat64 payload length or decoding time.",
        "type_and_value_roots": "Precisely named root indices from each declaration. Without storing/traversing the expression graph, no exact type-versus-value reachable-node size is claimed.",
        "new_declarations": "Only known-local-name/namespace candidates with origin caveat. Exact new-vs-challenge declaration set is unavailable under one-solution-stream scope."
    },
    "DAG_feasibility": {
        "format_supports_exact_graph": True,
        "within_fixed_budget_guaranteed": False,
        "reason": "ie records carry backward child indices, so a full compact child table plus per-root visited bitsets could compute unique root reachability in principle. Node count and repeated root closures are unmeasured: table space O(E), traversal time O(sum of root-reachable DAG sizes), not O(E) across all declarations. Python full objects or unrestricted memo sets can exceed256MiB. A memoized sum of child costs double-counts shared DAG nodes and must not be called exact DAG size. No exact per-root traversal is included in this bounded plan.",
        "selected_safe_scope": "Only streaming global/per-segment structural counts and explicit type/value root ids. No type/value proof-size claim."
    },
    "what_it_can_support": ["Locate old-v6 declarations associated with large first-emission serialization segments", "Rank old-v6 literal decimal bulk and emitted expression-constructor counts", "Separate literal-heavy definitions from declaration records with large type/value root references for further static review", "Verify the same historical export bytes during a single scan if it completes within limits"],
    "what_it_cannot_support": ["v8 elaboration time, peak RSS, killed phase, OOM attribution or particular failing declaration", "Runtime call counts, decoder allocation, Meta/kernel reduction cost, retained InfoTrees, compiler IR or emitted C costs", "Unused/dead declarations outside the selected exported root dependency closure", "An exact solution-minus-challenge diff without a challenge index/second full input pass", "Exact unique per-declaration type/value DAG size under this bounded default", "Any mathematical validation, source rewrite, successful compile or official acceptance"],
    "next_authorization": "No fullstream tool/helper is implemented or executed here. A later separately authorized metadata audit would require its own reviewed bounded implementation. This plan creates no enabled gate and changes no proof/state/counter/Git."
}
new(HERE / "plan.json", encode(plan))
readme = """# 旧v6导出：有限结构审计准备

本轮只读取每份导出前5行，核对已有小收据和exporter源码。677MB/349MB文件的完整SHA只引用原真实exit0收据，本轮没有重新hash或stream。当前stat大小与旧收据相同，但不能以此冒充当前全字节身份验证。

格式是lean4export3.1.0的逐行JSON。首行meta记录Lean版本/commit和exporter/format版本。`in`为名称索引、`il`为宇宙层级索引、`ie`为去重表达式索引；表达式通过子索引形成DAG。匿名名称0、zero level0是预置项。声明记录为def/thm/opaque/axiom/quot或inductive组，含名称、type/value等根索引。依赖先递归导出；表达式按结构去重、子表达式先出。默认剥除mdata，并把let的nonDep规范成false。natVal是十进制字符串，strVal是JSON字符串。源源码和原三根+primitives argv见report/plan。

这不是全部环境导出：原argv显式选择三个公开命题和规定primitives，递归dump其依赖；unsafe默认跳过。因而不存在于该闭包的旧dead消费者、宏decoder、InfoTree、LCNF和C不会由此直接显现。

严格方案只允许solution一次顺序流读（677296932B）；challenge仅现有前5行和小收据，不做第二大文件扫描。120秒总预算、256MiB进程内存、输出≤2MiB，输入过长行/名称表/内存/时间/格式异常均停止并标不完整，不重试。完整SHA可在同一次读取中累加，不能为hash再读一遍。

可重现的默认指标只有全局记录种类/字节数、natVal位数、每个声明的type/value根索引，以及`上一个声明结束→当前声明结束`的序列segment字节、表达式数和literal体积。segment并非该声明独占proofsize：共享DAG节点可能更早输出，递归依赖声明可能先取得节点归账，inductive以一组输出。不得把它拆称type/value精确大小。

格式足以在原则上建立完整DAG并对每个根做unique-reachable遍历；但677MB的节点数未知，O(E)存表与O(所有根闭包大小之和)遍历不能静态保证在256MiB/120秒内完成。重复相加子节点的memo量是展开树成本，会重复共享节点，不能冒称DAG大小。因此本固定方案不做root-reachable精确统计，只留根索引和segment代理。

新增声明只作“已知v6本地声明/namespace匹配”或origin_unresolved标签，没有challenge全名表时不能称精确差集。旧v6导出可以定位静态序列化体积线索，不能变成v8运行profile、Lean137/OOM归因、构建阶段/时间/RSS或数学通过证据。没有实施fullstream、Lean、kernel、export、源码变更、新数值/codec/checker族或新门。
"""
new(HERE / "README.zh.md", readme.encode())
for path, value in inputs.items():
    if path.read_bytes() != value:
        raise RuntimeError("Small input changed")
report = {"schema": "w9a2-export-cost-static-plan-evidence-v1", "scope": "Preparation only; each large export read at most first5 complete lines, no full-file hash/stream. No Lean/compiler/kernel/export/probe/API/network/process/UI/state/counter/Git action.", "exports": exports, "historical_v6_generation": generation, "historical_ordinary_exit_code": ordinary["exit_code"], "metadata_header": metadata, "exporter_source_pins_match_frozen_92cc": True, "small_inputs_before_after_unchanged": True, "small_inputs": [{"path": str(path), "bytes": len(value), "sha256": sha(value)} for path, value in inputs.items()], "full_streams_performed": 0, "mathematical_or_runtime_claim": False}
new(HERE / "report.json", encode(report))
members = []
for path in sorted(HERE.iterdir()):
    if path.is_file() and path.name != "files.json":
        value = path.read_bytes()
        members.append({"path": path.name, "bytes": len(value), "sha256": sha(value)})
new(HERE / "files.json", encode({"schema": "static-export-cost-plan-files-v1", "files": members}))
print(json.dumps({"result": "PREPARATION_ONLY", "files_manifest_sha256": sha((HERE / "files.json").read_bytes()), "report_sha256": sha((HERE / "report.json").read_bytes()), "prefix_bytes": {row["role"]: row["prefix_only"]["bytes"] for row in exports}, "full_streams": 0, "members": len(members)}))
