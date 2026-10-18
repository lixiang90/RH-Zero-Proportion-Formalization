"""Parse the one saved HTTP body; deliberately contains no networking imports."""
from pathlib import Path
from fractions import Fraction
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(__file__).resolve().parent
P = 3337839448633819172184136761695440236797
KAPPA = Fraction(P, 4955319193827760237900000000000000000000)
OLD = Fraction(P, 4955319193847235264050000000000000000000)


def sha(b):
    return hashlib.sha256(b).hexdigest()


def write_new(name, x):
    with (OUT / name).open("x", encoding="utf8", newline="\n") as f:
        json.dump(x, f, ensure_ascii=False, indent=2)
        f.write("\n")


def row(path):
    b = (ROOT / path).read_bytes()
    return {"path": path, "bytes": len(b), "sha256": sha(b)}


def exact(record):
    r = record["exactRational"]
    return Fraction(int(r["numerator"]), int(r["denominator"]))


def main():
    response = json.loads((OUT / "leaderboard.http.json").read_text("utf8"))
    body = (OUT / "leaderboard.body").read_bytes()
    assert len(body) == response["body_bytes"] and sha(body) == response["body_sha256"]
    data = json.loads(body)
    assert data["schemaVersion"] == 1 and data["track"] == "critical-line" and data["direction"] == "higher"
    records, current = data["records"], data["current"]
    accepted = [x for x in records if x.get("track") == "critical-line"
                and (x.get("formalVerification") is True or x.get("status") in ("published", "kernel-verified"))
                and isinstance(x.get("exactRational"), dict)]
    value = exact(current)
    assert value == max(exact(x) for x in accepted)
    prior_path = "tmp/goal-20261016/macro006-native-preproduction-fresh-record.json"
    prior_bytes = (ROOT / prior_path).read_bytes()
    prior = json.loads(prior_bytes)
    assert sha(prior_bytes) == "f03c572c86a9dd195eeb3742c570c4462b865c1c081b8112552469c7b3eb3510"
    with (OUT / "prior-snapshot.json").open("xb") as f:
        f.write(prior_bytes)
    headers = {k.lower(): v for k, v in response["response_headers"]}
    local_path = "research-goal-20261018-tiny-flatten-preparation-v3/draft/Solution.lean"
    local = (ROOT / local_path).read_bytes()
    assert response["status"] == 200 and headers.get("age") == "0" and headers.get("x-vercel-cache") == "MISS"
    write_new("parser-attempt.json", {
        "schema": "fresh-record-local-parser-attempt-v1",
        "original_source": row((OUT / "check_once.py").relative_to(ROOT).as_posix()),
        "exit_code": 1,
        "failure": "assert isinstance(records,list); actual API top-level object has current and records",
        "failure_happened_after_raw_HTTP_and_body_were_saved": True,
        "HTTP_response_count": 1,
        "local_finalizer_does_not_repeat_network_query": True,
    })
    result = {
        "schema": "independent-fresh-public-record-check-v1",
        "checked_at_utc": response["completed_at_utc"],
        "leaderboard_HTTP": response,
        "fresh_response_Age_zero": True,
        "cache_status": headers["x-vercel-cache"],
        "public_maximum_independently_matches_API_current": True,
        "records_in_response": len(records),
        "accepted_exact_critical_line_candidates": len(accepted),
        "accepted_selection": "critical-line; exact rational; formalVerification=true or status published/kernel-verified",
        "current_public_record": current,
        "record_R": str(value), "previous_record_R": str(OLD),
        "candidate_kappa": str(KAPPA),
        "candidate_minus_public_record": str(KAPPA - value),
        "record_changed_from_previous": value != OLD,
        "candidate_strictly_above_public_record": KAPPA > value,
        "public_record_equals_candidate": value == KAPPA,
        "body_identical_to_prior_snapshot": sha(body) == prior["body_sha256"],
        "current_metadata_identical_to_prior_snapshot": current == prior["current"],
        "local_v3_source": {**row(local_path), "trimmed_sha256": sha(local.strip())},
        "same_candidate_promotion_confirmed": False,
        "running_digest_reported_by_parent": "23e3dd…",
        "user_job_URL_available": False,
        "public_main_and_source_refetched": False,
        "no_source_refetch_reason": "Fresh public record, its full metadata and whole response body are unchanged; the conditional changed-record source check was not needed.",
        "public_main_current_commit_not_independently_requeried": True,
        "absence_of_public_acceptance_does_not_imply_user_job_failure": True,
        "network_rounds": 1,
        "HTTP_responses_received": 1,
        "pre_HTTP_sandbox_connection_failures": 1,
        "local_parser_failures_before_finalization": 1,
        "compiler_generator_mathematical_search_runs": 0,
        "old_frozen_files_changed": False,
    }
    assert value == OLD and result["body_identical_to_prior_snapshot"] and result["current_metadata_identical_to_prior_snapshot"]
    write_new("comparison.json", result)
    files = [row(p.relative_to(ROOT).as_posix()) for p in sorted(OUT.iterdir()) if p.is_file()]
    write_new("files.json", {"schema": "independent-fresh-record-files-v1", "files": files,
                             "read_dependencies": [row(local_path)],
                             "only_read_only_public_queries": True,
                             "public_record_unchanged": True,
                             "candidate_still_strictly_above": True,
                             "website_job_failure_inferred": False})
    print(json.dumps({"record_R": str(value), "candidate_kappa": str(KAPPA),
                      "candidate_strictly_above": KAPPA > value,
                      "record_id": current["id"], "status": current["status"],
                      "at_utc": response["completed_at_utc"],
                      "manifest": row((OUT / "files.json").relative_to(ROOT).as_posix())}))


if __name__ == "__main__":
    main()
