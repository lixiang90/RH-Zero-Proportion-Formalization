"""Freeze one complete independent G every-closure and fourstream review."""
from pathlib import Path
from hashlib import sha256
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent


def pin(path):
    raw=path.read_bytes()
    return {"path":path.relative_to(ROOT).as_posix(),"bytes":len(raw),"sha256":sha256(raw).hexdigest()}


def main():
    output=HERE/"audit-files.json"
    assert not output.exists() and not (HERE/"failure.json").exists()
    result=json.loads((HERE/"independent-review.json").read_text(encoding="utf-8"))
    assert result["passed"] and result["independent_executions"]==1
    assert result["complete_range_classified"] and result["committed_cases"]==5635876
    assert result["every_claimed_closed_case_verified"] and result["counts"]["unresolved"]==19838
    for row in result["inputs_sha256_end"]:assert pin(ROOT/row["path"])==row
    files=[pin(p) for p in sorted(HERE.iterdir()) if p.is_file()]
    prefix=HERE.relative_to(ROOT).as_posix()+"/"
    deps=[row for row in result["inputs_sha256_end"] if not row["path"].startswith(prefix)]
    manifest={"schema":"independent-G-complete-every-closure-fourstream-package-v1",
        "package_files":files,"total_package_bytes":sum(row["bytes"] for row in files),"dependency_files":deps,
        "independent_complete_audit_passed":True,"complete_range_classified":True,"committed_cases":5635876,
        "counts":result["counts"],"every_claimed_closed_case_verified":True,"frame_count":688,
        "all_four_stream_hashchain_index_bitmap_and_EOF_verified":True,
        "source_and_original_B_states_Mi_unchanged":True,"known_F_counted_as_G_closure":False,
        "unresolved_is_conservative_no_exclusion_only":True,"unresolved_set_nonempty_claimed":False,
        "producer_builtin_replay_failure_history_unchanged":True,"producer_Python_modules_imported":0,
        "BF_or_LP_or_optimizer_calls":0,"new_geometric_searches":0,"actual_kernel_values_computed":0,"Lean_runs":0,
        "scope":result["scope"],"new_global_joint_floor_proven":False,"new_unconditional_zero_proportion_proven":False,
        "whole_source_and_policy_runtime_budget":"unknown","website_submission_ready":False,"mutable_governance_dependency":False}
    with output.open("x",encoding="utf-8",newline="\n") as stream:
        json.dump(manifest,stream,ensure_ascii=False,indent=2);stream.write("\n")
    print(json.dumps(pin(output)))


if __name__=="__main__":main()
