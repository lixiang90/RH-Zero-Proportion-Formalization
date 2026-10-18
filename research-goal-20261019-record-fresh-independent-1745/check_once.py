"""One fresh public leaderboard round; no compiler, search, or producer imports."""
from pathlib import Path
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
import time
import urllib.request
import urllib.error

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(__file__).resolve().parent
P = 3337839448633819172184136761695440236797
KAPPA = Fraction(P, 4955319193827760237900000000000000000000)
OLD = Fraction(P, 4955319193847235264050000000000000000000)
LOCAL = "research-goal-20261018-tiny-flatten-preparation-v3/draft/Solution.lean"


def utc():
    return datetime.now(timezone.utc).isoformat()


def sha(b):
    return hashlib.sha256(b).hexdigest()


def write(name, b):
    with (OUT / name).open("xb") as f:
        f.write(b)


def js(name, x):
    write(name, (json.dumps(x, ensure_ascii=False, indent=2) + "\n").encode("utf8"))


def get(url, name):
    started = utc()
    request_headers = {"User-Agent": "independent-record-recheck/1.0",
                       "Cache-Control": "no-cache", "Pragma": "no-cache",
                       "Accept-Encoding": "identity"}
    request = urllib.request.Request(url, headers=request_headers)
    try:
        with urllib.request.urlopen(request, timeout=45) as response:
            body = response.read()
            status = response.status
            headers = list(response.headers.items())
            final_url = response.url
    except urllib.error.HTTPError as response:
        body = response.read()
        status = response.code
        headers = list(response.headers.items())
        final_url = response.url
    write(name + ".body", body)
    receipt = {"started_at_utc": started, "completed_at_utc": utc(),
               "request_url": url, "final_url": final_url,
               "request_headers": request_headers, "status": status,
               "response_headers": headers, "body_bytes": len(body), "body_sha256": sha(body)}
    js(name + ".http.json", receipt)
    write(name + ".headers.txt", (f"HTTP status {status}\r\n" + "".join(f"{k}: {v}\r\n" for k, v in headers)).encode("utf8"))
    assert status == 200, (name, status)
    return body, receipt


def exact(record):
    r = record.get("exactRational")
    return Fraction(int(r["numerator"]), int(r["denominator"])) if isinstance(r, dict) else None


def main():
    nonce = time.time_ns()
    body, receipt = get("https://www.riemannzeta.fun/api/leaderboard?independent1745=" + str(nonce), "leaderboard")
    records = json.loads(body)
    assert isinstance(records, list)
    accepted = [x for x in records if x.get("track") == "critical-line"
                and (x.get("formalVerification") is True or x.get("status") in ("published", "kernel-verified"))
                and exact(x) is not None]
    current = max(accepted, key=exact)
    value = exact(current)
    headers = {k.lower(): v for k, v in receipt["response_headers"]}
    local = (ROOT / LOCAL).read_bytes()
    result = {
        "schema": "independent-fresh-public-record-check-v1",
        "checked_at_utc": receipt["completed_at_utc"], "leaderboard": receipt,
        "fresh_response_Age_zero": headers.get("age") == "0",
        "cache_status": headers.get("x-vercel-cache"),
        "records_in_response": len(records), "accepted_exact_critical_line_candidates": len(accepted),
        "accepted_selection": "critical-line; exact rational; formalVerification=true or status published/kernel-verified",
        "current_public_record": current, "record_R": str(value),
        "previous_record_R": str(OLD), "candidate_kappa": str(KAPPA),
        "record_changed_from_previous": value != OLD,
        "candidate_strictly_above_public_record": KAPPA > value,
        "public_record_equals_candidate": value == KAPPA,
        "candidate_minus_public_record": str(KAPPA - value),
        "local_v3_source": {"path": LOCAL, "bytes": len(local), "sha256": sha(local),
                            "trimmed_sha256": sha(local.strip())},
        "running_digest_reported_by_parent": "23e3dd…",
        "job_URL_available": False,
        "absence_of_public_acceptance_does_not_imply_user_job_failure": True,
        "compiler_generator_mathematical_search_runs": 0,
        "public_main_and_source_fetched": False,
    }
    if value != OLD:
        # Source identity is required before treating a same-value record as our accepted result.
        _, main_receipt = get("https://api.github.com/repos/josusanmartin/riemann/commits/main?independent1745=" + str(nonce), "public-main")
        proof = current.get("proofUrl", "")
        assert proof.startswith("https://github.com/josusanmartin/riemann/blob/"), proof
        raw = proof.replace("https://github.com/", "https://raw.githubusercontent.com/", 1).replace("/blob/", "/", 1)
        source, source_receipt = get(raw, "public-record-source")
        result.update({"public_main_and_source_fetched": True, "public_main": main_receipt,
                       "public_record_source": source_receipt,
                       "public_source_exactly_matches_local_v3": source == local,
                       "public_source_trimmed_matches_local_v3": source.strip() == local.strip(),
                       "public_source_trimmed_sha256": sha(source.strip()),
                       "same_candidate_promotion_confirmed": value == KAPPA and source.strip() == local.strip()})
    else:
        result["public_main_source_not_refetched_reason"] = "Public maximum and its record metadata unchanged; no changed-source follow-up was needed in this single read-only round."
        result["same_candidate_promotion_confirmed"] = False
    js("comparison.json", result)
    files = []
    for p in sorted(OUT.iterdir()):
        if p.is_file():
            b = p.read_bytes()
            files.append({"path": p.relative_to(ROOT).as_posix(), "bytes": len(b), "sha256": sha(b)})
    js("files.json", {"schema": "independent-fresh-record-files-v1", "files": files,
                      "read_dependencies": [result["local_v3_source"]],
                      "only_read_only_public_queries": True, "website_job_failure_inferred": False})
    print(json.dumps({"current_record": str(value), "candidate_kappa": str(KAPPA),
                      "candidate_still_strictly_above": KAPPA > value,
                      "record_id": current.get("id"), "Age": headers.get("age"),
                      "cache": headers.get("x-vercel-cache"),
                      "manifest_sha256": sha((OUT / "files.json").read_bytes())}))


if __name__ == "__main__":
    main()
