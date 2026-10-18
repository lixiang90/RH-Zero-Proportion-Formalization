"""Freeze the successful, terminal one-run independent Stage B review."""
from pathlib import Path
from hashlib import sha256
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def pin(path):
    raw = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "bytes": len(raw), "sha256": sha256(raw).hexdigest()}


def main():
    output = HERE / "audit-files.json"
    assert not output.exists()
    review = json.loads((HERE / "independent-review.json").read_text(encoding="utf-8"))
    terminal = json.loads((HERE / "terminal.json").read_text(encoding="utf-8"))
    assert review["passed"] and terminal["exit_code"] == 0 and terminal["limit_stop"] is None
    assert terminal["child_launches"] == 1 and not terminal["failure_present"]
    assert not (HERE / "independent-failure.json").exists()
    for row in review["inputs_sha256_end"]:
        assert pin(ROOT / row["path"]) == row
    files = [pin(p) for p in sorted(HERE.iterdir()) if p.is_file()]
    prefix = HERE.relative_to(ROOT).as_posix() + "/"
    dependencies = [row for row in review["inputs_sha256_end"] if not row["path"].startswith(prefix)]
    result = {"schema": "independent-fixed-new-record-StageB-review-package-v1",
        "package_files": files, "total_package_bytes": sum(row["bytes"] for row in files),
        "dependency_files": dependencies,
        "one_independent_execution_terminal_exit_zero": True,
        "producer_Python_modules_imported": 0,
        "classification_counts": review["classification_counts"],
        "all13046_numeric_rows_and1187_full_exception_rows_equal": True,
        "all_original_48_roots_and70_nested_contracts_replayed": True,
        "all176_raised_root_outside_rows_equal": True,
        "canonical_all_node_trace_equal": True,
        "scope": review["scope"],
        "exception_pairs_scanned": 0, "new_kernel_queries": 0, "Lean_runs": 0,
        "complete_source_and_runtime_gate_passed": False,
        "new_joint_floor_proven": False, "new_unconditional_zero_proportion_proven": False,
        "website_submission_ready": False, "mutable_governance_dependency": False}
    with output.open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(result, stream, ensure_ascii=False, indent=2); stream.write("\n")
    print(json.dumps(pin(output)))


if __name__ == "__main__":
    main()
