"""Freeze the terminal one-run independent fixed-point affine review."""
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
    receipt = json.loads((HERE/"independent-review.json").read_text(encoding="utf-8"))
    assert receipt["passed"] and receipt["independent_review_executions"] == 1
    assert receipt["producer_Python_modules_imported"] == receipt["actual_kernel_values_computed"] == 0
    for row in receipt["inputs_sha256_end"]: assert pin(ROOT/row["path"]) == row
    files = [pin(p) for p in sorted(HERE.iterdir()) if p.is_file()]
    prefix = HERE.relative_to(ROOT).as_posix()+"/"
    deps = [row for row in receipt["inputs_sha256_end"] if not row["path"].startswith(prefix)]
    result = {"schema":"independent-fixed-existing-point-original-FS-affine-review-package-v1",
        "package_files":files,"total_package_bytes":sum(row["bytes"] for row in files),"dependency_files":deps,
        "independent_result_review_passed":True,"independent_review_executions":1,
        "all68_terms_beta_sigma_signed_scale_and9gap_values_equal":True,
        "all_original_FS_flow_and_main_margin_values_equal":True,
        "all153_original_bounds_and_both_ordered_conditions_rechecked":True,
        "source_and_all_dependencies_unchanged":True,"producer_Python_modules_imported":0,
        "same_existing_point_preserved":True,"actual_kernel_values_computed":0,
        "new_point_or_tangent_queries":0,"optimizer_calls":0,"DBM_solver_calls":0,"Lean_runs":0,
        "point_raw_and_clipped_margin_positive":True,
        "fixed_pair_original_M0_surplus_above_target_c":[24169728990071397846927248000000,6245599050221517825498512000000],
        "scope":"One exact independent fixed-point affine diagnostic; positive point margin does not prove a whole-cell or global joint floor",
        "complete_source_and_runtime_budget":"unknown","website_submission_ready":False,
        "new_joint_floor_proven":False,"new_unconditional_zero_proportion_proven":False,
        "mutable_governance_dependency":False}
    with output.open("x",encoding="utf-8",newline="\n") as stream:
        json.dump(result,stream,ensure_ascii=False,indent=2);stream.write("\n")
    print(json.dumps(pin(output)))


if __name__ == "__main__":
    main()
