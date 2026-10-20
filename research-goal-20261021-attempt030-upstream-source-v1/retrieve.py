"""One anonymous GET per two fixed upstream raw files; no proof execution."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import http.client
import json
import os
import ssl
import sys
import time

HERE = Path(__file__).resolve().parent
COMMIT = "94954faf2713ae9628d6fbca0ae24fe64370507c"
HOST = "raw.githubusercontent.com"
BASE = "/josusanmartin/riemann/" + COMMIT + "/submissions/attempt-030/"
BODY_LIMIT = 2_000_000
METADATA_LIMIT = 100_000
HEADER_LIMIT = 8_192
START = time.monotonic()
DEADLINE = START + 30.0
RESULTS = []


def require(ok, message):
    if not ok:
        raise ValueError(message)


def remaining():
    left = DEADLINE - time.monotonic()
    if left <= 0:
        raise TimeoutError("Shared 30-second retrieval deadline exceeded")
    return left


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")


def metadata_bytes():
    return sum(p.stat().st_size for p in HERE.rglob("*") if p.is_file()
               and p != HERE / "proof/Solution.lean")


def fetch(relative, limit):
    destination = HERE / relative
    require(not destination.exists(), "Fresh response path required")
    destination.parent.mkdir(parents=True, exist_ok=True)
    row = {"url": "https://" + HOST + BASE + relative, "method": "GET",
        "file": relative, "body_limit_bytes": limit, "GET_request_calls": 0,
        "started_at_UTC": datetime.now(timezone.utc).isoformat(),
        "HTTP_status": None, "headers_plain_strings": [], "Date_header_plain_string": "",
        "body_complete": False, "body_truncated": False,
        "bytes_saved": 0, "sha256_saved_bytes": None}
    RESULTS.append(row)
    connection = None
    response = None
    digest = hashlib.sha256()
    try:
        with destination.open("xb") as stream:
            try:
                connection = http.client.HTTPSConnection(HOST, timeout=remaining(), context=ssl.create_default_context())
                connection.auto_open = 0
                connection.connect()
                sock = connection.sock
                require(sock is not None, "No retained TLS socket")
                sock.settimeout(remaining())
                row["GET_request_calls"] += 1
                connection.request("GET", BASE + relative, headers={
                    "User-Agent": "Codex-fixed-public-source-read/1", "Accept-Encoding": "identity",
                    "Connection": "keep-alive"})
                sock.settimeout(remaining())
                response = connection.getresponse()
                row["HTTP_status"] = response.status
                headers = [[str(k), str(v)] for k, v in response.getheaders()]
                require(len(encoded(headers)) <= HEADER_LIMIT, "HTTP headers exceed bounded metadata capture")
                row["headers_plain_strings"] = headers
                row["Date_header_plain_string"] = next((v for k, v in headers if k.lower() == "date"), "")
                while True:
                    sock.settimeout(remaining())
                    block = response.read1(min(65536, limit - row["bytes_saved"] + 1))
                    if not block:
                        row["body_complete"] = True
                        break
                    room = limit - row["bytes_saved"]
                    kept = block[:room]
                    stream.write(kept)
                    digest.update(kept)
                    row["bytes_saved"] += len(kept)
                    if len(block) > room:
                        row["body_truncated"] = True
                        raise ValueError("Body exceeds bounded file cap; prefix preserved")
            finally:
                stream.flush()
                os.fsync(stream.fileno())
        remaining()
        require(row["HTTP_status"] == 200 and row["body_complete"], "HTTP response was not complete200")
        require(row["GET_request_calls"] == 1, "Exactly one GET per file required")
    finally:
        row["sha256_saved_bytes"] = digest.hexdigest()
        row["finished_at_UTC"] = datetime.now(timezone.utc).isoformat()
        if response is not None:
            response.close()
        if connection is not None:
            connection.close()


def main():
    require(not (HERE / "retrieval-observation.json").exists(), "Retrieval already recorded; never retry")
    require({p.name for p in HERE.iterdir()} == {"retrieve.py"}, "Fresh retrieval directory required")
    failure = None
    try:
        # Leave >=32KB for complete bounded headers, receipt, README and manifest.
        submission_limit = METADATA_LIMIT - metadata_bytes() - 32_000
        require(submission_limit > 0, "No remaining metadata budget")
        fetch("submission.json", submission_limit)
        fetch("proof/Solution.lean", BODY_LIMIT)
        remaining()
    except BaseException as exc:
        failure = {"type": type(exc).__name__, "message": str(exc)[:2000]}
    success = failure is None and len(RESULTS) == 2
    observation = {"schema": "two-fixed-upstream-raw-retrieval-v1", "commit": COMMIT,
        "scope": "Exact anonymous public source retrieval only; no proof validation, source transform or numerical decoder",
        "maximum_GET_calls": 2, "one_call_per_fixed_URL": True,
        "redirects_followed": 0, "automatic_retries": 0, "authorization_or_user_credentials_sent": False,
        "shared_budget_seconds": 30, "source_cap_bytes": BODY_LIMIT,
        "all_metadata_cap_bytes": METADATA_LIMIT,
        "raw_bodies_flushed_and_fsynced_before_any_source_or_submission_JSON_analysis": True,
        "Date_headers_are_plain_strings_not_parsed": True,
        "requests": RESULTS, "success_before_receipt": success, "failure": failure,
        "elapsed_seconds_before_receipt": time.monotonic() - START,
        "receipt_is_not_actual_outer_exit_evidence": True,
        "Lean_decoder_source_transform_state_Git_calls": 0}
    raw = encoded(observation)
    require(metadata_bytes() + len(raw) <= METADATA_LIMIT - 16_000, "Receipt exceeds reserved metadata budget")
    with (HERE / "retrieval-observation.json").open("xb") as stream:
        stream.write(raw)
        stream.flush()
        os.fsync(stream.fileno())
    finished = time.monotonic() - START
    actual_exit = 0 if success and finished <= 30.0 else 1
    print(json.dumps({"success": actual_exit == 0, "whole_elapsed_seconds": finished,
        "actual_exit_code_to_return": actual_exit, "failure": failure,
        "requests": [{k: row[k] for k in ("file", "HTTP_status", "GET_request_calls", "bytes_saved", "sha256_saved_bytes", "body_complete", "body_truncated")} for row in RESULTS],
        "observation_sha256": hashlib.sha256(raw).hexdigest()}))
    return actual_exit


if __name__ == "__main__":
    sys.exit(main())
