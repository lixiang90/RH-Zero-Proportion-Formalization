"""Local byte binding and additive manifest; no network or verifier execution."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(__file__).resolve().parent
EXPECTED_MANIFEST = "71f1ba7aaf1ba70b0edf1526103bdf0f1684a4b9c06fbcde3ac5e8a3edb0ebf2"
EXPECTED_JOB = "23e3dd765aa27de76938e056f13d3e0f08d849d0e7c39c6f78c62e7640c0a10f"


def sha(b):
    return hashlib.sha256(b).hexdigest()


def row(path):
    b = (ROOT / path).read_bytes()
    return {"path": path, "bytes": len(b), "sha256": sha(b)}


def write_new(name, obj):
    with (OUT / name).open("x", encoding="utf8", newline="\n") as f:
        json.dump(obj, f, ensure_ascii=False, indent=2)
        f.write("\n")


def main():
    prior = (OUT / "files.json").read_bytes()
    assert sha(prior) == EXPECTED_MANIFEST
    package = json.loads(prior)
    for r in package["files"] + package["read_dependencies"]:
        a = row(r["path"])
        assert a["bytes"] == r["bytes"] and a["sha256"] == r["sha256"], r["path"]
    manifest = (OUT / "accepted-submission.json.body").read_bytes()
    source = (OUT / "accepted-Solution.lean.body").read_bytes()
    job_digest = sha(b"submission.json\0" + manifest + b"proof/Solution.lean\0" + source)
    comparison = json.loads((OUT / "comparison.json").read_text("utf8"))
    assert job_digest == EXPECTED_JOB
    assert comparison["this_candidate_promoted_to_public_record"] is True
    assert comparison["raw_source_byte_equal_to_uploaded_v3"] is True
    assert comparison["UI_trimmed_source_byte_equal_to_uploaded_v3"] is True
    verification = {
        "schema": "accepted-upload-digest-independent-byte-binding-v1",
        "original_package": {"path": (OUT / "files.json").relative_to(ROOT).as_posix(),
                             "bytes": len(prior), "sha256": EXPECTED_MANIFEST},
        "official_manifest": row((OUT / "accepted-submission.json.body").relative_to(ROOT).as_posix()),
        "official_source": row((OUT / "accepted-Solution.lean.body").relative_to(ROOT).as_posix()),
        "digest_algorithm": "SHA256(UTF8('submission.json') || 0x00 || manifest_raw || UTF8('proof/Solution.lean') || 0x00 || solution_raw)",
        "official_raw_upload_digest": job_digest,
        "user_reported_running_digest": EXPECTED_JOB,
        "exact_digest_match": True,
        "raw_uploaded_v3_source_match": True,
        "UI_normalized_uploaded_v3_source_match": True,
        "accepted_public_record_is_this_user_submission": True,
        "original_package_unchanged": sha((OUT / "files.json").read_bytes()) == EXPECTED_MANIFEST,
        "public_elapsed_or_private_job_details_available": False,
        "additional_network_compiler_solver_runs": 0,
    }
    write_new("digest-verification.json", verification)
    files = [row(p.relative_to(ROOT).as_posix()) for p in sorted(OUT.iterdir()) if p.is_file()]
    assert max(r["bytes"] for r in files) <= 2000000
    write_new("accepted-files.json", {
        "schema": "independent-official-acceptance-with-upload-digest-files-v1",
        "files": files,
        "read_dependencies": package["read_dependencies"],
        "official_public_record_equals_this_candidate": True,
        "accepted_source_exactly_uploaded_v3": True,
        "public_manifest_source_digest_equals_reported_user_job": True,
        "original_files_manifest_preserved": EXPECTED_MANIFEST,
        "native_v4_not_used_or_needed_for_identity": True,
        "compiler_solver_or_new_search_runs": 0,
    })
    print(json.dumps({"manifest": row((OUT / "accepted-files.json").relative_to(ROOT).as_posix()),
                      "file_count": len(files), "file_bytes": sum(x["bytes"] for x in files),
                      "digest_verified": job_digest, "original_package_preserved": True}))


if __name__ == "__main__":
    main()
