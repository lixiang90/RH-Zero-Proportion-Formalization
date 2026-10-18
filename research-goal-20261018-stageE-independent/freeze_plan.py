"""Freeze a static review plan only; no E geometry, point or pair evaluation."""
from pathlib import Path
from hashlib import sha256
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def pin(path):
    raw = path.read_bytes()
    return {"path":path.relative_to(ROOT).as_posix(),"bytes":len(raw),"sha256":sha256(raw).hexdigest()}


def main():
    out = HERE/"plan-files.json"
    assert not out.exists()
    dependencies = [ROOT/path for path in [
        "research-goal-20261018-stageB-classification/files.json",
        "research-goal-20261018-stageB-independent/audit-files.json",
        "research-goal-20261018-stageC-dbm/files.json",
        "research-goal-20261018-stageC-independent/audit-files.json",
        "research-goal-20261018-stageD-independent/audit-files.json",
        "research-goal-20261018-joint-affine-static/review-files.json",
        "research-goal-20261018-joint-affine-flow-proof/proof-files.json"]]
    data = {"schema":"StageE-independent-result-review-strategy-only-v1",
        "package_files":[pin(HERE/"PLAN.zh.md"),pin(Path(__file__))],
        "dependency_manifests":[pin(path) for path in dependencies],
        "scope":"Static strategy; feasible witness check or complete independent all-closed certificate replay remains conditional on root E decision and frozen producer result",
        "StageE_cases_evaluated":0,"pair_scans":0,"kernel_queries":0,"optimizer_calls":0,"Lean_runs":0,
        "new_joint_floor_proven":False,"website_submission_ready":False,"mutable_governance_dependency":False}
    with out.open("x",encoding="utf-8",newline="\n") as stream:
        json.dump(data,stream,ensure_ascii=False,indent=2);stream.write("\n")
    print(json.dumps(pin(out)))


if __name__ == "__main__":
    main()
