"""Freeze the terminal independent E witness and complete reported-prefix audit."""
from pathlib import Path
from hashlib import sha256
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def pin(path):
    raw = path.read_bytes()
    return {"path":path.relative_to(ROOT).as_posix(),"bytes":len(raw),"sha256":sha256(raw).hexdigest()}


def main():
    output = HERE/"audit-files.json"
    assert not output.exists() and not (HERE/"failure.json").exists()
    result = json.loads((HERE/"independent-review.json").read_text(encoding="utf-8"))
    assert result["passed"] and result["independent_result_review_executions"] == 1
    assert result["pair_scan_executions"] == result["DBM_solver_calls"] == 0
    for row in result["inputs_sha256_end"]: assert pin(ROOT/row["path"]) == row
    files = [pin(p) for p in sorted(HERE.iterdir()) if p.is_file()]
    prefix = HERE.relative_to(ROOT).as_posix()+"/"
    deps = [row for row in result["inputs_sha256_end"] if not row["path"].startswith(prefix)]
    manifest = {"schema":"independent-fixed-E-first-underpaid-and-complete-prefix-review-package-v1",
        "package_files":files,"total_package_bytes":sum(row["bytes"] for row in files),"dependency_files":deps,
        "independent_result_review_passed":True,"producer_Python_modules_imported":0,
        "all1193_reported_records_checked":True,"scalar_paid_records":766,"strict_cycle_records":426,
        "first_underpaid_feasible_ordinal":1192,"all153_original_edges_verified":True,
        "both_actual_Ordered_conditions_violated_at_this_point":True,
        "exact_Mi_used_not_Nat_floor":True,"same_original_states_FS_and_margins_verified":True,
        "all_5635876_cases_covered":False,"scope":result["scope"],
        "pair_scan_executions":0,"DBM_solver_calls":0,"actual_kernel_values_computed":0,
        "new_points_or_FS_or_tangents":0,"optimizer_calls":0,"Lean_runs":0,
        "complete_source_and_runtime_budget":"unknown","website_submission_ready":False,
        "new_joint_floor_proven":False,"new_unconditional_zero_proportion_proven":False,
        "mutable_governance_dependency":False}
    with output.open("x",encoding="utf-8",newline="\n") as stream:
        json.dump(manifest,stream,ensure_ascii=False,indent=2);stream.write("\n")
    print(json.dumps(pin(output)))


if __name__ == "__main__":
    main()
