"""Small closed-receipt/source read only; never reads the NDJSON input."""
from pathlib import Path
import hashlib
import json
import os

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SCAN = ROOT / "research-goal-20261020-w9a2-export-cost-scan-v1"
paths = [ROOT / "research-goal-20261020-w9a2-export-cost-plan-formal/run_stream.py",
         SCAN / "scan/result.json", SCAN / "outer-observation.json",
         SCAN / "stdout.txt", SCAN / "stderr.txt"]
values = {path: path.read_bytes() for path in paths}
sha = lambda raw: hashlib.sha256(raw).hexdigest()
result = json.loads(values[paths[1]])
outer = json.loads(values[paths[2]])
if sha(values[paths[0]]) != "643c444d659d280f13068d2cde597acd467900e8b0264258363c1e9efcedc122":
    raise RuntimeError("Runner pin mismatch")
if sha(values[paths[1]]) != outer["result_sha256"] or outer["actual_child_exit_code"] != 1 or outer["timeout"] is not False:
    raise RuntimeError("Closed failure receipt mismatch")
if result["complete"] is not False or result["success"] is not False or result["error_type"] != "ValueError" or result["error"] != "Name-table budget exceeded":
    raise RuntimeError("Unexpected failure")
if result["observed_peak_RSS_bytes"] != 56147968:
    raise RuntimeError("Wrong RSS")
report = {
    "schema": "w9a2-export-cost-scan-independent-v1",
    "scope": "Only frozen16KiB runner and closed small result/outer/stdout/stderr read. No large NDJSON input, full hash, stream, API/process/network/Lean/compiler/kernel/export/solver call. No change to source/receipt/state/counter/Git; no v2 proposal.",
    "result": "FAILED_PREPARATORY_STRUCTURE_SCAN_NO_COMPLETE_DATA",
    "actual_small_receipt": {"child_exit_code": outer["actual_child_exit_code"], "outer_elapsed_seconds": outer["elapsed_seconds"], "timeout": outer["timeout"], "inner_elapsed_seconds": result["elapsed_seconds"], "observed_peak_RSS_bytes": result["observed_peak_RSS_bytes"], "observed_peak_RSS_MiB": result["observed_peak_RSS_bytes"] / 1048576, "error_type": result["error_type"], "error": result["error"], "complete": False},
    "parent_original_tool_observation": {"scope": "Reported directly by root in task; raw original tool result was not supplied as an extra local file for this review", "session": 53230, "terminal_tool_chunk": "008e11", "actual_original_outer_exit_code_reported": 1},
    "static_diagnosis": [
        {"runner_lines_1based": [16, 102, 162, 166], "fact": "Every in/name record resolves its full parent prefix plus dot and suffix into a new Python string. The accumulated name_bytes estimate starts with list/empty-string sizes and adds sys.getsizeof(resolved)+16 for each candidate name. The32MiB NAME_CAP check throws before appending the name that would exceed the estimate."},
        {"runner_lines_1based": [87, 96, 164, 166], "fact": "This is an independent accounting budget for expanded-name retention, not the256MiB observed-RSS stop and not the120s deadline. It is an estimate with a16B per-name allowance, not an exact allocator/heap measurement. It includes the name whose estimate causes failure even though that name has not yet been appended."},
        {"runner_lines_1based": [148, 166], "fact": "The name table is maintained for all names encountered in the dependency-closed export, before any declaration's known-namespace/origin classification. Repeated full prefixes are stored in separate resolved strings. The error therefore reflects this scanner representation's fixed capacity being exhausted."},
        {"runner_lines_1based": [228, 257, 263, 268], "fact": "The exception bypassed EOF/full SHA comparison and successful global/segment/root output. The failure handler only serialized the error, elapsed and sampled peak RSS. It did not preserve the terminating name, byte offset, number of names, partial counters or rankings."}
    ],
    "positive_support": "Only that this particular name-expanding metadata scanner hit its predeclared32MiB name-accounting budget after about20s, with observed own RSS53.55MiB and a real child nonzero. No rescanning is authorized by this report.",
    "not_supported": ["A completed input byte count or freshly verified677MB SHA", "Any complete/partial declaration, expression, type/value, literal or segment ranking", "Which declaration/name/namespace caused the stop", "That candidate-local rather than imported names dominate", "Lean/compiler interpreter RSS, retained InfoTrees, an OOM diagnosis or the v8 official Lean137 cause", "A need or permission to increase a limit, rescan, change data structures, proof source or mathematical route"],
    "success_flags": {"scan_complete": False, "mathematical_validation": False, "compiler_or_kernel_execution_by_this_review": False, "official_acceptance": False},
    "README_availability": "No scan README was present at first read. Per task, review did not wait for one or claim to have reviewed a later file.",
    "inputs": [{"path": str(path), "bytes": len(value), "sha256": sha(value)} for path, value in values.items()]
}
for path, value in values.items():
    if path.read_bytes() != value:
        raise RuntimeError("Small input changed")
report["input_hashes_before_after_equal"] = True
def new(path, value):
    with path.open("xb") as stream:
        stream.write(value); stream.flush(); os.fsync(stream.fileno())
def encode(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()
new(HERE / "review.json", encode(report))
new(HERE / "README.zh.md", ("本次结构扫描真实失败：child1，外层记录20.563s且非timeout；result在20.422s报告Name-table budget exceeded，采样自身峰RSS56147968B（53.55MiB）。\n\n停止原因是scanner把所有namespace的名称逐条展开成完整Python字符串，累计sys.getsizeof(resolved)+16估算超过固定32MiB名称表门；在新名称append前抛错。它不是256MiB RSS上限触发，也不是Lean内存测量。共享前缀被重复展开的存储策略解释了此scanner容量门的含义，但没有终止名称/offset/计数，不能定位来源或给出定量归因。\n\nEOF、完整677MB hash、完整字节计数和任何排名均未生成。不能由此推出大data/proofsize、哪个声明/namespace、Lean137/OOM或v8编译内存瓶颈。原始外层session53230/008e11真实exit1来自root直接报告；本包独立读取的小outer文件确认child1，不冒充自行读到原始工具结果。\n\n仅核小runner/result/outer/空stdout与stderr，未读大NDJSON。原README当时未生成，按令未等待。没有更改原收据、runner、proof、state、counter或Git，没有设计v2/加预算/重扫。\n").encode())
members = []
for path in sorted(HERE.iterdir()):
    if path.is_file() and path.name != "files.json":
        value = path.read_bytes(); members.append({"path": path.name, "bytes": len(value), "sha256": sha(value)})
new(HERE / "files.json", encode({"schema": "export-cost-failed-scan-independent-files-v1", "files": members}))
print(json.dumps({"manifest_sha256": sha((HERE / "files.json").read_bytes()), "review_sha256": sha((HERE / "review.json").read_bytes()), "large_input_bytes_read": 0, "members": len(members)}))
