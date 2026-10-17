"""Hash preserved public policy bytes; no proof or discovery computation."""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def row(path):
    raw = path.read_bytes()
    return {"path": str(path.relative_to(ROOT)).replace("\\", "/"),
            "bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}


def main():
    output = HERE / "policy-files.json"
    assert not output.exists(), "Do not overwrite frozen policy evidence"
    snapshot = json.loads((HERE / "policy-snapshot.json").read_bytes())
    for item in snapshot["files"]:
        actual = row(ROOT / item["path"])
        assert all(actual[k] == item[k] for k in actual)
    paths = [ROOT / x["path"] for x in snapshot["files"]]
    paths += [HERE / name for name in (
        "NOTE.txt", "policy-snapshot.json", "fetch_policy.py", "freeze_policy.py")]
    files = [row(path) for path in paths]
    result = {"schema": "current-website-generator-policy-static-review-v1",
              "upstream_commit": snapshot["commit"], "package_files": files,
              "package_bytes": sum(x["bytes"] for x in files),
              "production_Comparator_timeout_seconds": 3200,
              "outer_job_timeout_seconds": 3240,
              "production_memory_limit_established_here": False,
              "pure_Lean_witness_discovery_not_explicitly_prohibited_in_reviewed_policy": True,
              "policy_acceptance_is_inference_not_tested_guarantee": True,
              "new_generator_implemented": False, "new_optimizer_executed": False,
              "Lean_compilations": 0, "exports_or_nanoda_runs": 0,
              "website_proof_uploads": 0,
              "source_size_or_runtime_feasibility_proven": False,
              "new_global_energy_floor_proven": False,
              "new_unconditional_zero_proportion_proven": False,
              "website_submission_ready": False}
    raw = (json.dumps(result, indent=2) + "\n").encode()
    output.write_bytes(raw)
    print(json.dumps({"manifest_sha256": hashlib.sha256(raw).hexdigest(),
                      "files": len(files), "bytes": result["package_bytes"]}))


if __name__ == "__main__":
    main()
