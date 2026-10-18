"""Freeze the successful one-run independent Stage A finite replay."""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def row(path):
    raw = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest()}


def main():
    out = HERE / "audit-files.json"
    assert not out.exists(), "Preserve frozen manifests"
    replay = json.loads((HERE / "independent-replay.json").read_text(encoding="utf-8"))
    assert replay["passed"] and not (HERE / "independent-failure.json").exists()
    for item in replay["inputs_sha256_end"]:
        assert row(ROOT / item["path"]) == item
    files = [row(HERE / name) for name in ["replay_independent.py", "NOTE.zh.md",
        "independent-started.json", "independent-replay.json", "freeze_package.py"]]
    dependencies = [item for item in replay["inputs_sha256_end"] if not item["path"].startswith(HERE.relative_to(ROOT).as_posix() + "/")]
    out.write_text(json.dumps({
        "schema": "independent-original-s1R13-StageA-finite-replay-package-v1",
        "package_files": files, "dependency_files": dependencies,
        "one_execution_exit_zero": True, "producer_Python_modules_imported": 0,
        "all48_roots_and70_nested_contracts_replayed": True,
        "all160_original_WZ_guards_replayed": True,
        "canonical_all_node_trace_equal": True,
        "scope": "Original finite argument and guard replay only; source analytic proofs and Lean acceptance retained as separate obligations",
        "new_threshold_classification": False, "new_kernel_anchors": 0,
        "solver_calls": 0, "Lean_runs": 0,
        "new_global_floor_proven": False, "website_submission_ready": False},
        ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(row(out), ensure_ascii=False))


if __name__ == "__main__":
    main()
