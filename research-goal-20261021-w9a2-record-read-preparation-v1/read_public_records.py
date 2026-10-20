"""FUTURE one-GET public records read. Prepared only; no execution authorized here."""
from pathlib import Path
from fractions import Fraction
import argparse
import base64
import hashlib
import http.client
import json
import os
import re
import ssl
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
OUTPUT_PREFIX = ROOT / "research-goal-20261021-w9a2-record-read-output"
HOST = "api.github.com"
API_PATH = "/repos/josusanmartin/riemann/contents/data/records.json?ref=main"
BODY_LIMIT = 2_000_000
ANALYSIS_LIMIT = 256_000
TIMEOUT_SECONDS = 30
K = Fraction(3337881639516708570682858853672166187793,
             4955348542279967171490000000000000000000)
RULE_PATH = "research-goal-20261020-w9a2-source-normalization-review/source/src/lib/records.ts"
RULE_SHA = "1fab4d48cac4e67dadc8f529034c05bcb4b5c908f7fb1527cd13de9edbb740c7"
SCHEMA_PATH = "research-goal-20261020-w9a2-source-normalization-review/source/src/lib/challenge.ts"
SCHEMA_SHA = "847d503e9a0427d2bfe1fd0c8d92d31b42ade54bdeb98a6b8e29f1894284f53e"
TRACKS = {"critical-line", "simple-critical-line", "distinct-zeros"}
STATUSES = {"published", "claimed", "ci-passed", "kernel-verified"}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha256(raw):
    return hashlib.sha256(raw).hexdigest()


def json_bytes(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")


def write_new(path, raw):
    with path.open("xb") as stream:
        stream.write(raw)
        stream.flush()
        os.fsync(stream.fileno())


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON object key")
        result[key] = value
    return result


def load_json(raw):
    return json.loads(raw.decode("utf-8"), object_pairs_hook=unique_object)


def exact_fraction(value):
    require(type(value) is dict and set(value) == {"numerator", "denominator"}, "Exact rational object shape")
    for field in ("numerator", "denominator"):
        item = value[field]
        require(type(item) is str and 1 <= len(item) <= 200 and re.fullmatch(r"[1-9][0-9]*", item) is not None,
                "Exact rational integers must be positive canonical strings, at most200 digits")
    return Fraction(int(value["numerator"]), int(value["denominator"]))


def fraction_json(value):
    return {"numerator": str(value.numerator), "denominator": str(value.denominator)}


def validate_and_compare(records):
    require(type(records) is list and len(records) > 0, "Records must be a nonempty JSON list")
    ids = set()
    exact = {}
    critical = []
    for index, record in enumerate(records):
        require(type(record) is dict, "Record must be an object")
        record_id = record.get("id")
        require(type(record_id) is str and re.fullmatch(r"[a-z0-9][a-z0-9-]*", record_id) is not None,
                "Invalid record id")
        require(record_id not in ids, "Duplicate record id")
        ids.add(record_id)
        require(record.get("track") in TRACKS and record.get("status") in STATUSES, "Unknown record track/status")
        require("exactRational" in record, "Missing exactRational field; null must be explicit")
        require(type(record.get("formalVerification")) is bool, "formalVerification must be a boolean")
        if record["exactRational"] is not None:
            exact[index] = exact_fraction(record["exactRational"])
        if record["track"] == "critical-line":
            critical.append(index)
    kernel = [i for i in critical if records[i]["status"] == "kernel-verified"]
    published = [i for i in critical if records[i]["status"] == "published"]
    # Captured records.ts: last kernel-verified in array order, else last published.
    eligible = kernel if kernel else published
    require(eligible, "No eligible critical-line current record")
    current_index = eligible[-1]
    current = records[current_index]
    kernel_exact = [i for i in kernel if i in exact]
    missing = [{"index": i, "id": records[i]["id"], "status": records[i]["status"]}
               for i in kernel if i not in exact]
    maximum = max((exact[i] for i in kernel_exact), default=None)
    current_value = exact.get(current_index)
    current_gt = K > current_value if current_value is not None else None
    all_exact_gt = all(K > exact[i] for i in kernel_exact)
    comparison_passed = current_gt is True and all_exact_gt
    current_info = {"index": current_index, "id": current["id"], "status": current["status"],
        "exactRational": current["exactRational"],
        "normalized_fraction": fraction_json(current_value) if current_value is not None else None,
        "K_strictly_greater": current_gt}
    return {
        "schema": "fresh-public-records-exact-comparison-v1",
        "validation_scope": "Nonempty records list, unique ids, known track/status, boolean formalVerification, and positive exactRational fractions; not a full Zod record/date validation",
        "selection_rule": "critical-line filter; last kernel-verified in original array order, otherwise last published; NOT decimal/date sorting",
        "record_count": len(records), "critical_line_count": len(critical),
        "critical_line_kernel_verified_count": len(kernel),
        "critical_line_kernel_verified_exact_count": len(kernel_exact),
        "critical_line_kernel_verified_missing_exact": missing,
        "current": current_info, "K": fraction_json(K),
        "max_critical_line_kernel_verified_exact": {
            "fraction": fraction_json(maximum),
            "record_ids": [records[i]["id"] for i in kernel_exact if exact[i] == maximum]
        } if maximum is not None else None,
        "K_strictly_greater_than_all_critical_line_kernel_verified_exact": all_exact_gt,
        "exact_comparison_gate_passed": comparison_passed,
        "all_kernel_verified_critical_records_compared_exactly": not missing,
        "missing_exact_current_record": current_value is None,
        "missing_exact_entries_are_unknown_not_inferred_from_decimals": True,
        "full_record_superiority_claimed": False,
        "official_submission_or_acceptance_or_quota_checked": False
    }


def prepared_pins():
    pre_path = HERE / "pre-execution-files.json"
    pre_raw = pre_path.read_bytes()
    pre = load_json(pre_raw)
    require(pre["execution_authorized"] is False and pre["helper_executed"] is False,
            "Frozen preparation scope differs")
    require({row["path"] for row in pre["files"]} == {"read_public_records.py", "README.zh.md"},
            "Prepared file allowlist differs")
    pins = []
    for row in pre["files"]:
        raw = (HERE / row["path"]).read_bytes()
        require(len(raw) == row["bytes"] and sha256(raw) == row["sha256"], "Prepared helper/document changed")
        pins.append({"path": str((HERE / row["path"]).relative_to(ROOT)).replace("\\", "/"),
                     "bytes": len(raw), "sha256": sha256(raw)})
    pins.append({"path": str(pre_path.relative_to(ROOT)).replace("\\", "/"),
                 "bytes": len(pre_raw), "sha256": sha256(pre_raw)})
    for relative, expected in ((RULE_PATH, RULE_SHA), (SCHEMA_PATH, SCHEMA_SHA)):
        raw = (ROOT / relative).read_bytes()
        require(sha256(raw) == expected, "Captured selection/schema source changed")
        pins.append({"path": relative, "bytes": len(raw), "sha256": expected})
    return pins


def main():
    t0 = time.monotonic()
    started_epoch_ns = time.time_ns()
    parser = argparse.ArgumentParser(description="One public GitHub GET; preserve raw response before parsing")
    parser.add_argument("--output", required=True, help="New simple leaf name under the fixed workspace output prefix")
    args = parser.parse_args()
    require(re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]{0,79}", args.output) is not None,
            "Output must be a simple fresh leaf name")
    pins = prepared_pins()
    workspace = ROOT.resolve()
    require(not OUTPUT_PREFIX.is_symlink(), "Output prefix must not be a symlink")
    require(OUTPUT_PREFIX.resolve().is_relative_to(workspace), "Output prefix escapes workspace")
    OUTPUT_PREFIX.mkdir(exist_ok=True)
    destination = OUTPUT_PREFIX / args.output
    require(not destination.exists() and not destination.is_symlink(), "Fresh output leaf required; never overwrite/retry")
    destination.mkdir(exist_ok=False)
    require(destination.resolve().is_relative_to(OUTPUT_PREFIX.resolve()), "Output leaf escapes fixed prefix")
    raw_path = destination / "response.raw.json"
    raw_hash = hashlib.sha256()
    raw_count = 0
    raw_complete = False
    raw_truncated = False
    request_calls = 0
    status = None
    response_headers = []
    header_date = ""
    analysis = None
    analysis_pin = None
    decoded_pin = None
    api_blob_sha1 = None
    calculated_blob_sha1 = None
    failure = None
    connection = None
    response = None
    nonce = str(started_epoch_ns)
    path = API_PATH + "&_codex_nonce=" + nonce
    url = "https://" + HOST + path

    def remaining():
        left = TIMEOUT_SECONDS - (time.monotonic() - t0)
        if left <= 0:
            raise TimeoutError("30-second total adoption deadline exceeded")
        return left

    try:
        # Create/preserve raw output even if DNS/TLS/headers fail. No response JSON
        # or HTTP Date parsing occurs until after this body stream is closed/fsynced.
        with raw_path.open("xb") as raw_stream:
            try:
                connection = http.client.HTTPSConnection(HOST, timeout=remaining(), context=ssl.create_default_context())
                connection.auto_open = 0
                connection.connect()
                tls_socket = connection.sock
                require(tls_socket is not None, "HTTPS socket unavailable")
                tls_socket.settimeout(remaining())
                request_calls += 1
                connection.request("GET", path, headers={"User-Agent": "Codex-public-record-read/1",
                    "Accept": "application/vnd.github+json", "Accept-Encoding": "identity",
                    "Cache-Control": "no-cache", "Pragma": "no-cache", "Connection": "keep-alive",
                    "X-GitHub-Api-Version": "2022-11-28"})
                tls_socket.settimeout(remaining())
                response = connection.getresponse()
                status = response.status
                response_headers = [[str(k), str(v)] for k, v in response.getheaders()]
                header_date = next((v for k, v in response_headers if k.lower() == "date"), "")
                while True:
                    tls_socket.settimeout(remaining())
                    block = response.read1(min(65536, BODY_LIMIT - raw_count + 1))
                    if not block:
                        raw_complete = True
                        break
                    room = BODY_LIMIT - raw_count
                    kept = block[:room]
                    raw_stream.write(kept)
                    raw_hash.update(kept)
                    raw_count += len(kept)
                    if len(block) > room:
                        raw_truncated = True
                        raise ValueError("HTTP body exceeds2MB; only bounded raw prefix retained")
            finally:
                raw_stream.flush()
                os.fsync(raw_stream.fileno())
        # RAW BODY HAS BEEN SAVED. All response/API/record parsing starts here.
        remaining()
        require(raw_complete and status == 200, "HTTP response is not complete200; no record facts adopted")
        require(request_calls == 1, "Exactly one GET call required")
        payload = load_json(raw_path.read_bytes())
        require(type(payload) is dict and payload.get("type") == "file"
                and payload.get("path") == "data/records.json" and payload.get("encoding") == "base64",
                "GitHub contents response identity/encoding differs")
        api_blob_sha1 = payload.get("sha")
        require(type(api_blob_sha1) is str and re.fullmatch(r"[0-9a-f]{40}", api_blob_sha1) is not None,
                "API Git blob SHA1 shape")
        content = payload.get("content")
        require(type(content) is str, "API content must be base64 text")
        compact = re.sub(r"[ \t\r\n]", "", content)
        decoded = base64.b64decode(compact.encode("ascii"), validate=True)
        require(base64.b64encode(decoded).decode("ascii") == compact, "Noncanonical base64")
        require(len(decoded) <= BODY_LIMIT and type(payload.get("size")) is int and payload["size"] == len(decoded),
                "Decoded content size differs")
        calculated_blob_sha1 = hashlib.sha1(b"blob " + str(len(decoded)).encode("ascii") + b"\0" + decoded).hexdigest()
        require(calculated_blob_sha1 == api_blob_sha1, "Decoded Git blob identity differs from API sha")
        write_new(destination / "records.decoded.json", decoded)
        decoded_pin = {"path": "records.decoded.json", "bytes": len(decoded), "sha256": sha256(decoded),
                       "git_blob_sha1": calculated_blob_sha1}
        remaining()
        records = load_json(decoded)
        analysis = validate_and_compare(records)
        analysis_raw = json_bytes(analysis)
        require(len(analysis_raw) <= ANALYSIS_LIMIT, "Comparison analysis exceeds bounded output; do not truncate unknown entries")
        write_new(destination / "analysis.json", analysis_raw)
        analysis_pin = {"path": "analysis.json", "bytes": len(analysis_raw), "sha256": sha256(analysis_raw)}
        for pin in pins:
            require(sha256((ROOT / pin["path"]).read_bytes()) == pin["sha256"], "Prepared input changed")
        remaining()
        require(analysis["exact_comparison_gate_passed"], "K does not strictly exceed current exact and every available critical-line kernel-verified exact record, or current exact is unknown")
    except BaseException as exc:
        failure = {"type": type(exc).__name__, "message": str(exc)[:2000]}
    finally:
        if response is not None:
            response.close()
        if connection is not None:
            connection.close()
    elapsed = time.monotonic() - t0
    accepted = failure is None and elapsed <= TIMEOUT_SECONDS and analysis is not None and analysis["exact_comparison_gate_passed"]
    if not accepted and failure is None:
        failure = {"type": "DeadlineExceeded", "message": "Receipt preparation crossed30-second adoption budget"}
    receipt = {
        "schema": "one-get-public-record-read-receipt-v1", "url": url,
        "scope": "Public main records retrieval and scoped exact comparisons only; no private website auth/quota/submit/proof",
        "started_local_epoch_ns": started_epoch_ns, "elapsed_seconds_before_receipt": elapsed,
        "budget_seconds": TIMEOUT_SECONDS, "GET_request_call_count": request_calls,
        "automatic_retries": 0, "redirects_followed": 0, "HTTP_status": status,
        "HTTP_headers_plain_strings": response_headers, "HTTP_Date_header_raw": header_date,
        "HTTP_Date_header_present": bool(header_date), "HTTP_Date_was_parsed": False,
        "raw_body": {"path": "response.raw.json", "bytes_saved": raw_count, "sha256_saved_bytes": raw_hash.hexdigest(),
                     "complete": raw_complete, "truncated_at_2MB": raw_truncated,
                     "saved_before_response_JSON_or_Date_conversion": True},
        "API_blob_sha1": api_blob_sha1, "calculated_decoded_blob_sha1": calculated_blob_sha1,
        "decoded_file": decoded_pin, "analysis_file": analysis_pin,
        "captured_records_selection_rule_source": {"path": RULE_PATH, "sha256": RULE_SHA,
            "captured_commit": "1135c0386310a0a038004d3b0fe64d0237e47dce", "fresh_source_rules_retrieved": False},
        "prepared_input_pins": pins, "exact_comparison_gate_passed": bool(accepted),
        "receipt_is_not_actual_outer_exit_evidence": True,
        "adoption_requires_actual_outer_exit0_and_whole_elapsed_at_most30": True,
        "missing_exact_entries_remain_unknown": True, "full_record_superiority_claimed": False,
        "new_R_claimed_without_validated_body": False,
        "official_quota_or_auth_or_submission_or_acceptance_observed": False,
        "error": failure
    }
    receipt_raw = json_bytes(receipt)
    # The original root must also observe actual exit0 and whole elapsed<=30s;
    # a saved positive receipt is not substituted for that outer observation.
    write_new(destination / "receipt.json", receipt_raw)
    finished = time.monotonic() - t0
    actual_exit = 0 if accepted and finished <= TIMEOUT_SECONDS else 1
    print(json.dumps({"destination": str(destination), "receipt_sha256": sha256(receipt_raw),
        "whole_elapsed_seconds": finished, "exact_comparison_gate_passed": actual_exit == 0,
        "HTTP_status": status, "GET_request_call_count": request_calls, "error": failure}))
    return actual_exit


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as exc:
        # Preflight rejects invalid/existing destinations without touching them
        # and without making a GET. Once fresh output exists, main saves receipts.
        print(json.dumps({"preflight_or_receipt_failure": type(exc).__name__, "message": str(exc)[:2000],
            "no_record_facts_adopted": True}), file=sys.stderr)
        sys.exit(1)
