"""Freeze source-backed original raw-dual recovery, preserving producer failure."""
from pathlib import Path
from hashlib import sha256
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent


def pin(path):
    raw=path.read_bytes()
    return {"path":path.relative_to(ROOT).as_posix(),"bytes":len(raw),"sha256":sha256(raw).hexdigest()}


def main():
    out=HERE/"audit-files.json"
    assert not out.exists() and not (HERE/"failure.json").exists()
    result=json.loads((HERE/"independent-review.json").read_text(encoding="utf-8"))
    assert result["passed"] and result["independent_executions"]==1 and result["dual_only_valid_lower_recovered"]
    assert result["producer_failure_preserved"] and result["producer_primal_invalid"]
    for row in result["inputs_sha256_end"]:assert pin(ROOT/row["path"])==row
    assert pin(HERE/"recovered-lower-certificate.json")["sha256"]==result["recovered_certificate_sha256"]
    files=[pin(p) for p in sorted(HERE.iterdir()) if p.is_file()]
    prefix=HERE.relative_to(ROOT).as_posix()+"/"
    deps=[row for row in result["inputs_sha256_end"] if not row["path"].startswith(prefix)]
    manifest={"schema":"independent-fixed-F-source-backed-original-raw-dual-Lower-package-v1",
        "package_files":files,"total_package_bytes":sum(row["bytes"] for row in files),"dependency_files":deps,
        "source_rebuild_and_independent_review_passed":True,"all155_source_rows_and_objective_equal":True,
        "all68_original_FS_terms_and_flow_equal":True,"original_primal_violated_rows":38,
        "original_raw_dual_full10_balance_nonnegative_and_pays_target":True,"dual_support_count":9,
        "dual_only_Lower_certificate_recovered":True,"primal_optimum_claimed":False,"producer_failure_preserved":True,
        "producer_Python_modules_imported":0,"Sympy_imported":False,"LP_or_optimizer_calls":0,
        "new_points_or_FS_or_tangents":0,"actual_kernel_values_computed":0,"Lean_runs":0,
        "scope":result["scope"],"all_other_exception_pairs_handled":False,"new_global_joint_floor_proven":False,
        "new_unconditional_zero_proportion_proven":False,"complete_source_and_runtime_budget":"unknown",
        "website_submission_ready":False,"mutable_governance_dependency":False}
    with out.open("x",encoding="utf-8",newline="\n") as stream:
        json.dump(manifest,stream,ensure_ascii=False,indent=2);stream.write("\n")
    print(json.dumps(pin(out)))


if __name__=="__main__":main()
