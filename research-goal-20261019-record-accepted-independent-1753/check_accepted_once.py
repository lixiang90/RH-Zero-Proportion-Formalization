"""One independent public-acceptance round; raw accepted source is never rewritten."""
from pathlib import Path
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
import time
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(__file__).resolve().parent
LOCAL = "research-goal-20261018-tiny-flatten-preparation-v3/draft/Solution.lean"
LOCAL_SHA = "024902a7ef01ccba2a6c71e54682a31712417e5d3c0b4ead5f6f80ad25fd1a81"
P = 3337839448633819172184136761695440236797
Q = 4955319193827760237900000000000000000000
KAPPA = Fraction(P, Q)
JS_TRIM = "\u0009\u000b\u000c\u0020\u00a0\u1680\u2000\u2001\u2002\u2003\u2004\u2005\u2006\u2007\u2008\u2009\u200a\u202f\u205f\u3000\ufeff\u000a\u000d\u2028\u2029"


def sha(b):
    return hashlib.sha256(b).hexdigest()


def write(name, b):
    with (OUT / name).open("xb") as f:
        f.write(b)


def js(name, obj):
    write(name, (json.dumps(obj, ensure_ascii=False, indent=2) + "\n").encode("utf8"))


def utc():
    return datetime.now(timezone.utc).isoformat()


def get(url, name, max_bytes):
    started = utc()
    req_headers = {"Cache-Control": "no-cache", "Pragma": "no-cache",
                   "Accept-Encoding": "identity", "User-Agent": "independent-accepted-record-check/1.0"}
    req = urllib.request.Request(url, headers=req_headers)
    with urllib.request.urlopen(req, timeout=45) as response:
        body = response.read(max_bytes + 1)
        assert len(body) <= max_bytes, (name, len(body))
        status, headers, final = response.status, list(response.headers.items()), response.url
    assert status == 200, (name, status)
    write(name + ".body", body)
    receipt = {"started_at_utc": started, "completed_at_utc": utc(), "request_url": url,
               "request_headers": req_headers, "final_url": final, "status": status,
               "response_headers": headers, "body_bytes": len(body), "body_sha256": sha(body)}
    js(name + ".http.json", receipt)
    write(name + ".headers.txt", (f"HTTP status {status}\r\n" + "".join(f"{k}: {v}\r\n" for k, v in headers)).encode("utf8"))
    return body, receipt


def raw_url(url):
    assert url.startswith("https://github.com/josusanmartin/riemann/blob/"), url
    return url.replace("https://github.com/", "https://raw.githubusercontent.com/", 1).replace("/blob/", "/", 1)


def trim(b):
    return b.decode("utf8").strip(JS_TRIM).encode("utf8")


def main():
    body, api = get("https://www.riemannzeta.fun/api/leaderboard?accepted1753=" + str(time.time_ns()), "leaderboard", 1000000)
    data = json.loads(body)
    assert isinstance(data, dict) and data["track"] == "critical-line" and data["direction"] == "higher"
    current = data["current"]
    r = current["exactRational"]
    value = Fraction(int(r["numerator"]), int(r["denominator"]))
    headers = {k.lower(): v for k, v in api["response_headers"]}
    print(json.dumps({"API_at_utc": api["completed_at_utc"], "record_id": current["id"],
                      "exactRational": r, "status": current["status"],
                      "formalVerification": current.get("formalVerification"),
                      "author": current.get("author"), "github": current.get("github"),
                      "proofUrl": current.get("proofUrl"), "Age": headers.get("age"),
                      "cache": headers.get("x-vercel-cache"), "equals_candidate_kappa": value == KAPPA}), flush=True)
    assert headers.get("age") == "0" and headers.get("x-vercel-cache") == "MISS"
    assert value == KAPPA, "Unexpected public value; retain raw response and report without chasing a new target"
    assert current["status"] == "kernel-verified" and current.get("formalVerification") is True
    source, source_receipt = get(raw_url(current["proofUrl"]), "accepted-Solution.lean", 2000000)
    submission, submission_receipt = get(raw_url(current["sourceUrl"]), "accepted-submission.json", 1000000)
    local = (ROOT / LOCAL).read_bytes()
    assert sha(local) == LOCAL_SHA
    accepted = json.loads(submission)
    result = {
        "schema": "independent-official-accepted-candidate-check-v1",
        "checked_at_utc": api["completed_at_utc"], "leaderboard_HTTP": api,
        "current_public_record": current, "public_exact_R": str(value),
        "candidate_exact_kappa": str(KAPPA), "public_record_equals_candidate": value == KAPPA,
        "accepted_status": current["status"], "formalVerification": current["formalVerification"],
        "public_source_commit": current["proofUrl"].split("/blob/", 1)[1].split("/", 1)[0],
        "accepted_source_HTTP": source_receipt,
        "accepted_submission_HTTP": submission_receipt,
        "accepted_submission_metadata": accepted,
        "local_uploaded_v3": {"path": LOCAL, "bytes": len(local), "sha256": sha(local),
                              "UI_trimmed_bytes": len(trim(local)), "UI_trimmed_sha256": sha(trim(local))},
        "public_accepted_source": {"bytes": len(source), "sha256": sha(source),
                                   "UI_trimmed_bytes": len(trim(source)), "UI_trimmed_sha256": sha(trim(source))},
        "UI_normalization": "UTF-8 decode, ECMAScript String.trim whitespace/line-terminator set, UTF-8 encode",
        "raw_source_byte_equal_to_uploaded_v3": source == local,
        "UI_trimmed_source_byte_equal_to_uploaded_v3": trim(source) == trim(local),
        "this_candidate_promoted_to_public_record": value == KAPPA and trim(source) == trim(local),
        "do_not_chase_strictly_above_own_accepted_kappa": True,
        "native_v4_source_used_for_identity": False,
        "compiler_generator_solver_or_search_runs": 0,
        "old_frozen_files_or_root_rounds_changed": False,
    }
    js("comparison.json", result)
    files = []
    for p in sorted(OUT.iterdir()):
        if p.is_file():
            b = p.read_bytes()
            files.append({"path": p.relative_to(ROOT).as_posix(), "bytes": len(b), "sha256": sha(b)})
    js("files.json", {"schema": "independent-official-acceptance-files-v1", "files": files,
                      "read_dependencies": [result["local_uploaded_v3"]],
                      "official_public_record_observed": True,
                      "same_uploaded_v3_identity_confirmed": result["this_candidate_promoted_to_public_record"]})
    print(json.dumps({"official_record_promoted": result["this_candidate_promoted_to_public_record"],
                      "raw_equal": source == local, "UI_trim_equal": trim(source) == trim(local),
                      "public_source_sha256": sha(source), "public_source_bytes": len(source),
                      "manifest_sha256": sha((OUT / "files.json").read_bytes())}), flush=True)


if __name__ == "__main__":
    main()
