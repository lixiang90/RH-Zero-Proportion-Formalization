"""Freeze the terminal one-run independent fixed Stage C result review."""
from pathlib import Path
from hashlib import sha256
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def pin(path):
    raw = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "bytes": len(raw), "sha256": sha256(raw).hexdigest()}


def main():
    out = HERE / "audit-files.json"
    assert not out.exists() and not (HERE / "failure.json").exists()
    receipt = json.loads((HERE / "independent-review.json").read_text(encoding="utf-8"))
    assert receipt["passed"] and receipt["independent_review_executions"] == 1
    assert receipt["pair_scan_executions"] == receipt["DBM_solver_calls"] == 0
    for row in receipt["inputs_sha256_end"]:
        assert pin(ROOT / row["path"]) == row
    files = [pin(p) for p in sorted(HERE.iterdir()) if p.is_file()]
    prefix = HERE.relative_to(ROOT).as_posix() + "/"
    dependencies = [row for row in receipt["inputs_sha256_end"] if not row["path"].startswith(prefix)]
    result = {"schema": "independent-StageC-fixed-first-feasible-review-package-v1",
        "package_files": files, "total_package_bytes": sum(row["bytes"] for row in files),
        "dependency_files": dependencies, "independent_result_review_passed": True,
        "producer_Python_modules_imported": 0, "pair_scan_executions": 0, "DBM_solver_calls": 0,
        "case0_given_strict_cycle_checked": True, "case1_all153_edges_checked": True,
        "both_actual_ordered_conditions_hold": True, "both_original_fixed_FS_flow_and_margins_equal": True,
        "source_and_all_dependencies_unchanged": True,
        "scope": receipt["scope"], "actual_kernel_energy_evaluated_at_potential": False,
        "new_kernel_queries": 0, "optimizer_calls": 0, "Lean_runs": 0,
        "complete_source_and_runtime_budget": "unknown", "complete_source_gate_passed": False,
        "new_joint_floor_proven": False, "new_unconditional_zero_proportion_proven": False,
        "website_submission_ready": False, "mutable_governance_dependency": False}
    with out.open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(result, stream, ensure_ascii=False, indent=2); stream.write("\n")
    print(json.dumps(pin(out)))


if __name__ == "__main__":
    main()
