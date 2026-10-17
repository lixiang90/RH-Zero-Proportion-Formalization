"""Freeze the completed coefficient experiment and two separate exact audits."""
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
    output = HERE / "decomposition-files.json"
    assert not output.exists(), "Do not overwrite frozen evidence"
    worker = ROOT / "research-goal-20261017-ninepoint-worker-audit/audit-files.json"
    assert row(worker)["sha256"] == "dcda20afd7956c412fe2d445ca52814acbc21834ec0f3d4a997f19d3fe5e0cec"
    audit = json.loads(worker.read_bytes())
    assert audit["passed"] and audit["strict_dual_obstruction_for_fixed_H_and_direct_c9_sum_lambda_certificate"]
    for item in audit["package_files"] + audit["dependency_files"]:
        actual = row(ROOT / item["path"])
        assert actual["sha256"] == item["sha256"]
        if "bytes" in item:
            assert actual["bytes"] == item["bytes"]
    root_audit = ROOT / "research-goal-20261017-ninepoint-decomposition-audit/independent-replay.json"
    assert row(root_audit)["sha256"] == "920e299b475fd62c1b999d570ea9e85cf0df3f7eba4a674121b1e300def4a307"
    data = json.loads(root_audit.read_bytes())
    assert data["passed"] and not data["solver_output_optimality_assumed"]
    for item in data["dependency_files"] + [data["source"]]:
        assert row(ROOT / item["path"]) == item
    paths = [HERE / name for name in (
        "support_obstruction.py", "support-obstruction.json", "coefficient_gluing.py",
        "coefficient-gluing.json", "coefficient_gluing_presolver_failed.py",
        "presolver-failure.json", "NOTE.zh.md", "freeze_package.py")]
    paths += [root_audit, root_audit.with_name("verify.py"), worker]
    paths += [ROOT / item["path"] for item in audit["package_files"]]
    files = [row(path) for path in paths]
    dependencies = [row(ROOT / path) for path in (
        "GramDefect20261015/Core.lean", "GramDefect20261015/SharpWindow.lean",
        "StructuralResearch20261016/W10RefinedCandidate.lean",
        "StructuralW10Cert20261016/FinalConditional.lean")]
    result = {"schema": "fixed-global-ninepoint-decomposition-evidence-v1",
              "package_files": files, "package_bytes": sum(x["bytes"] for x in files),
              "dependency_files": dependencies,
              "support_obstruction_passed": True,
              "one_coefficient_solver_call": True, "pre_solver_failed_execution_preserved": True,
              "root_separate_stdlib_replay_passed": True,
              "independent_worker_stdlib_replay_passed": True,
              "dual_scope": "Fixed H and direct c9*sum(lambda) linear reuse of the ten deletion embeddings. This does not bound the stronger actual joint minimum of a glued ledger.",
              "stronger_joint_floor_not_ruled_out": True,
              "fixed_direct_linear_reuse_family_stopped": True,
              "new_Lean_invocations": 0, "actual_kernel_evaluations": 0, "tree_records_read": 0,
              "new_global_floor_proven": False,
              "new_unconditional_zero_proportion_proven": False,
              "website_submission_ready": False,
              "mutable_governance_state_hashed": False}
    raw = (json.dumps(result, indent=2) + "\n").encode()
    output.write_bytes(raw)
    print(json.dumps({"manifest_sha256": hashlib.sha256(raw).hexdigest(),
                      "package_files": len(files), "package_bytes": result["package_bytes"]}))


if __name__ == "__main__":
    main()
