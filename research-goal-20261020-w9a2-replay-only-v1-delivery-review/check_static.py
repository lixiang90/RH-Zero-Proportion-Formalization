"""Read-only static cross-review; never import/execute any proof runner."""
import ast
import hashlib
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
PACK = ROOT / "research-goal-20261020-w9a2-replay-only-v1"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads(path.read_bytes())


def pin(path):
    return {"path": path.relative_to(ROOT).as_posix(), "bytes": path.stat().st_size, "sha256": sha(path)}


def abs_path(value):
    item = Path(value)
    return Path(os.path.abspath(item if item.is_absolute() else ROOT / item))


def save(name, value):
    with (HERE / name).open("xb") as output:
        output.write((json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode())


def main():
    sources = [PACK / name for name in ["files.json", "run_replay.py", "gate-proposal.json", "README.zh.md", "static-preparation.json"]]
    sources += [ROOT / "research-goal-20261020-w9a2-verification-preparation-v1/run_verification.py"]
    before = {str(path): pin(path) for path in sources}
    assert sha(PACK / "files.json") == "d5552f25ba8b77332ff275b931b529d5e771456663950da90fc6a69348622ade"
    for row in load(PACK / "files.json")["files"]:
        file = PACK / row["path"]
        assert sha(file) == row["sha256"] and file.stat().st_size == row["bytes"]
    runner = PACK / "run_replay.py"
    assert sha(runner) == "f9048bc8bb320a895894df4aaf2d82a6b1e5b79b4da05600fb9184330237791c"
    tree = ast.parse(runner.read_bytes())
    roles = next(ast.literal_eval(node.value) for node in tree.body if isinstance(node, ast.Assign)
        and any(isinstance(target, ast.Name) and target.id == "RUNTIME_ROLES" for target in node.targets))
    attribute_calls = {node.func.attr for node in ast.walk(tree) if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)}
    assert not ({"execute", "ordinary", "proof_replays", "finish", "setup_runtime", "generate_sources"} & attribute_calls)
    gate = load(PACK / "gate-proposal.json")
    assert gate["allow_replay_execution"] is False and gate["proposal_only"] is True
    assert gate["cold_full_3200s_passed"] is False and gate["official_website_acceptance"] is False and gate["submitted"] is False
    assert sha(sources[-1]) == "92cc8dcf3e3c46e76490ba7bfe8d93bc10e331131eaab3b4c3ae500f80ac66a8"
    extra = []
    for key in ["original_gate", "original_failed_archive", "source", "frozen_source", "coreaudit_source", "runtime_closure"]:
        row = gate[key]; item = abs_path(row["path"])
        assert sha(item) == row["sha256"] and ("bytes" not in row or item.stat().st_size == row["bytes"])
        extra.append(item)
    oldgate = load(abs_path(gate["original_gate"]["path"]))
    assert gate["runtime"] == {key: oldgate["runtime"][key] for key in gate["runtime"]}
    archive = abs_path(gate["original_failed_archive"]["path"]).parent
    archive_rows = load(archive / "files.json")["files"]
    for row in archive_rows:
        item = archive / row["path"]
        assert sha(item) == row["sha256"] and item.stat().st_size == row["bytes"]
        extra.append(item)
    failure = load(archive / "job/failure.json")
    raw = load(archive / "original-parent-exit.json")
    assert failure["error_type"] == "TimeoutExpired" and failure["local_fullchain_verified"] is False
    assert raw["session"] == 68962 and raw["parent_pid"] == 49320 and raw["actual_original_handle_result"]["exit_code"] == 1
    assert len(failure["ordinary_printed_axioms"]) == 15
    assert all(set(value) <= {"propext", "Quot.sound", "Classical.choice"} for value in failure["ordinary_printed_axioms"].values())
    for label, row in gate["existing_exports"].items():
        terminal = load(archive / ("job/logs/" + label + "-native-export.terminal.json"))
        stages = [stage for stage in failure["stages"] if stage["label"] == label + "-native-export"]
        assert stages == [terminal] and terminal["exit_code"] == 0
        assert terminal["output_sha256"] == row["sha256"] and terminal["output_bytes"] == row["bytes"]
        assert abs_path(terminal["output"]) == abs_path(row["path"])
    closure = load(abs_path(gate["runtime_closure"]["path"]))
    runtime = gate["runtime"]
    sdk = abs_path(runtime["lean_sysroot"])
    sdk_prefix = str(sdk).casefold() + os.sep
    nano = abs_path(runtime["nanoda"]["host_binary"]["path"])
    direct = {abs_path(runtime[key]["path"]) for key in ["lean", "python_controller", "wsl_executable", "taskkill_executable"]} | {nano}
    selected = {}
    sdk_count = 0
    for row in closure["files"]:
        item = abs_path(row["path"])
        is_sdk = str(item).casefold().startswith(sdk_prefix)
        if not (is_sdk or row.get("role") in roles or item in direct) or row["path"].startswith("/mnt/"):
            continue
        sdk_count += int(is_sdk)
        key = str(item).casefold()
        assert key not in selected
        selected[key] = row
    assert sdk_count == 13951 and len(selected) == 14194
    tool = abs_path(runtime["interpreted_tool_libs"][0])
    expected = {"Comparator.olean", "Comparator/Axioms.olean", "Comparator/Compare.olean", "Comparator/Util.olean", "Export/Parse.olean"}
    assert {item.relative_to(tool).as_posix() for item in tool.rglob("*") if item.is_file()} == expected
    assert all(str(tool / name).casefold() in selected for name in expected)
    assert all(str(item).casefold() in selected for item in direct)
    assert gate["tool_commits"] == closure["tool_commits"]
    assert abs_path(gate["source"]["path"]).read_bytes() == abs_path(gate["frozen_source"]["path"]).read_bytes()
    assert before == {str(path): pin(path) for path in sources}
    report = {"scope": "Static source/AST, immutable small-source/archive hash and runtime-selection metadata review only",
        "result": "PASS_STATIC_NO_DEFINITE_BLOCKER_FOUND", "runner": pin(runner),
        "preparation_manifest": pin(PACK / "files.json"), "gate_proposal": pin(PACK / "gate-proposal.json"),
        "sdk_metadata_selection_count": sdk_count, "total_runtime_metadata_selection_count": len(selected),
        "five_interpreted_modules_include_nested_Parse": True, "old_actual_timeout_archive_rows_hash_verified": len(archive_rows),
        "all_source_before_after_pins_equal": True, "source_input_pins": list(before.values()),
        "additional_small_input_pins": [pin(path) for path in dict.fromkeys(extra)],
        "reviewed_contracts": [
            "Typed disabled proposal; enabled gate can differ only in two authorization booleans; new exclusive work and sole root owner",
            "Original exact source and both real exit0 exports bound to archived original actual exit1 TimeoutExpired; 15 ordinary roots retained",
            "SDK plus direct loader/Python/tool/Nano byte pins verified inside future timer, without package cache imports or candidate recompilation/export",
            "Only old92cc run/cleanup/IO/environment/deadline methods reused; original fullPASS execute/ordinary/proof_replays/finish never invoked",
            "Sequential unchanged CoreAudit 3messages and actual exit0, then serial Nano --wait/config/actual successful declaration count and permitted axioms",
            "One new monotonic3200 deadline spans bootstrap, pins, both mathematical replays, posthashes and three fsynced receipts; original-handle actual exit0 still required",
            "Cold3200 remains false in new success/failure receipts; separate mathematical replay and official acceptance scopes remain distinct",
        ],
        "limits": [
            "No runner, legacy module, metadata assembler, compiler, exporter, kernel or collector was imported/executed.",
            "Current SDK/large-export bytes were not independently rehashed in this static review; future runner performs those bound checks before and after replay.",
            "Sole proof-process ownership is a root authorization precondition; runner uses exclusive work and owned process cleanup, not a global process lock.",
            "No mathematical replay, local cold PASS or official result is claimed.",
        ], "proof_or_runner_or_collector_runs": 0}
    save("review.json", report)
    save("files.json", {"scope": report["scope"], "files": [{"path": path.name, "bytes": path.stat().st_size, "sha256": sha(path)}
        for path in sorted(HERE.iterdir()) if path.is_file() and path.name != "files.json"], "proof_runs": 0})
    print(json.dumps({"manifest_sha256": sha(HERE / "files.json"), "result": report["result"],
        "runtime_selection": len(selected), "runner_executed": False, "proof_runs": 0}), flush=True)


if __name__ == "__main__":
    main()
