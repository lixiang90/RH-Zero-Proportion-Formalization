"""Independent static material audit; does not import or execute author scripts."""
from pathlib import Path
from fractions import Fraction
import hashlib
import json
import os
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PREP = ROOT / "submission/w9a2-weighted-potential-20261020-prepared-v7"
WIRE = ROOT / "submission/w9a2-weighted-potential-20261020-expected-wire-v7"
OUTER = ROOT / "research-goal-20261020-w9a2-submission-materials-v7-preparation"
CAP = ROOT / "research-goal-20261020-w9a2-source-normalization-review"
SOURCE_SHA = "dae01f6844642d7f9ee8180616c1f57aefc18ab8616bc8a4a46a14bf8e9fefc6"
DIGEST = "1f28020dcda27176a97f8c48e9c9d3f9dc00107ce904f1a1f6706b1f43309771"
IDENT = "lixiang90-w9a2-weighted-potential-v7-20261020"
INPUTS = {}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def read(path):
    data = path.read_bytes()
    key = path.relative_to(ROOT).as_posix()
    row = {"path": key, "bytes": len(data), "sha256": sha(data)}
    require(key not in INPUTS or INPUTS[key] == row, "Input changed during read")
    INPUTS[key] = row
    return data


def obj(path):
    return json.loads(read(path))


def check_manifest(base, expected_sha, expected_count):
    raw = read(base / "files.json")
    require(sha(raw) == expected_sha, "Manifest pin mismatch")
    packet = json.loads(raw)
    require(len(packet["files"]) == expected_count, "Manifest row count mismatch")
    seen = set()
    for row in packet["files"]:
        path = (base / row["path"]).resolve()
        require(path.is_relative_to(base.resolve()) and path not in seen, "Invalid manifest membership")
        seen.add(path)
        data = read(path)
        require(len(data) == row["bytes"] and sha(data) == row["sha256"], "Manifest file mismatch")
    return packet


def write_new(name, value):
    data = (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()
    with (HERE / name).open("xb") as stream:
        stream.write(data)
        stream.flush()
        os.fsync(stream.fileno())
    return data


def main():
    require(not (HERE / "review.json").exists() and not (HERE / "files.json").exists(), "Exclusive output exists")
    pm = check_manifest(PREP, "91c5e7c812e92dddfcf9c4d26fe5061c0fd1d8bb8d50aa69aa29c021cfcc724a", 13)
    wm = check_manifest(WIRE, "6ea94c6f7d2a02ed64de70a4a349ffa210d61e5a77098aec255aef32cc265a46", 2)
    check_manifest(OUTER, "83c18d0fc19040497d893538abf43d4c7f79f8aae375c8cd32fe00b6ec34f298", 6)
    source = read(PREP / "proof/Solution.lean")
    require(len(source) == 1829242 and sha(source) == SOURCE_SHA, "Proof source mismatch")
    require(source == read(ROOT / "research-goal-20261020-w9a2-delivery/draft-v7/Solution.lean"), "Draft/source copy mismatch")
    require(source.count(b"\r\n") == 221 and source.count(b"\r") == 221 and source.endswith(b"\n") and not source.endswith(b"\n\n"), "Source normalization mismatch")
    require(not re.search(rb"(?m)^#print axioms ", source), "Removed diagnostic command remains")
    manifest = obj(PREP / "submission.draft.json")
    fields = obj(PREP / "website-fields.draft.json")
    status = obj(PREP / "verification-status.json")
    policy = obj(PREP / "source-wire-policy.json")
    math = obj(PREP / "mathematical-source-check.json")
    prediction = obj(WIRE / "prediction.json")
    require(manifest["id"] == fields["proposed_id"] == fields["suggested_result_name"] == IDENT, "ID mismatch")
    require(len(IDENT) <= 80 and re.fullmatch(r"[a-z0-9][a-z0-9-]*", IDENT), "ID schema mismatch")
    require(manifest["author"] == {"github": "lixiang90", "displayName": "Li Xiang"}, "Author mismatch")
    require(fields["public_display_name"] == "Li Xiang" and fields["authenticated_GitHub_login"] == "lixiang90", "UI identity mismatch")
    require(manifest["model"] is None and fields["AI_model_optional"] is None and fields["model_field_value"] == "", "Model null mismatch")
    require(manifest["harness"] == fields["coding_harness_optional"] == "Codex", "Harness mismatch")
    summary = manifest["summary"]
    old_manifest = obj(ROOT / "submission/w9a2-weighted-potential-20261020-prepared-v6/submission.draft.json")
    require(summary == fields["summary"] == old_manifest["summary"] and len(summary) == 605 and len(summary.encode("utf-16-le")) // 2 == 605, "Summary mismatch")
    require(manifest["method"] == fields["method"] == old_manifest["method"], "Method mismatch")
    score = {"numerator": "3337881639516708570682858853672166187793", "denominator": "4955348542279967171490000000000000000000"}
    require(manifest["score"] == fields["score"] == old_manifest["score"] == score, "Exact score mismatch")
    ratio = Fraction(int(score["numerator"]), int(score["denominator"]))
    H = Fraction(6721237468782417141365717707344332375586, 10**40)
    B = Fraction(454741897490, 10**14)
    c = Fraction(4465145772003282851, 5 * 10**20)
    require((H - B) / (1 - c) == ratio and math["values_from_historical_v6"]["kappa"] == str(ratio), "Inherited rational description mismatch")
    require(score["numerator"].encode() in source and score["denominator"].encode() in source, "Exact score absent from source")
    expected = {"schemaVersion": 1, "id": IDENT, "track": "critical-line",
                "author": {"github": "lixiang90", "displayName": "Li Xiang"}, "score": score,
                "proof": {"solution": "proof/Solution.lean", "theorem": "candidate_critical_line_bound",
                          "cumulativeTheorem": "candidate_critical_line_bound_cumulative", "improvementTheorem": "candidate_strict_improvement"},
                "summary": summary, "method": fields["method"], "model": None, "harness": "Codex", "license": "Apache-2.0"}
    encoded = (json.dumps(expected, ensure_ascii=False, indent=2) + "\n").encode()
    require(manifest == expected and list(manifest) == list(expected), "Server field values/order mismatch")
    require(encoded == read(PREP / "submission.draft.json") == read(WIRE / "expected-server-submission.json"), "JSON.stringify-compatible byte mismatch")
    require(len(encoded) == 1343 and sha(encoded) == "7d78afb3d25847b89bd0d4daae06daec52e55e8a39524f82431599bbf21d70f6", "Server manifest pin mismatch")
    digest = sha(b"submission.json\0" + encoded + b"proof/Solution.lean\0" + source)
    require(digest == DIGEST == prediction["expected_job_proofDigest"], "Combined wire digest mismatch")
    captured_manifest_raw = read(CAP / "files.json")
    require(sha(captured_manifest_raw) == "4209625bb670f556ccabbf3b46a31deed8a67178951d4a8524be551406ec3432", "Captured protocol manifest pin mismatch")
    captured = {row["path"]: row for row in json.loads(captured_manifest_raw)["files"]}
    server_path = CAP / "source/src/lib/direct-submission.ts"
    schema_path = CAP / "source/src/lib/challenge.ts"
    for path in (server_path, schema_path):
        data = read(path)
        row = captured[path.relative_to(ROOT).as_posix()]
        require(sha(data) == row["sha256"] and len(data) == row["bytes"], "Captured server source pin mismatch")
    server = read(server_path).decode()
    require('.update("submission.json\\0")' in server and '.update("proof/Solution.lean\\0")' in server and 'JSON.stringify(submission, null, 2)' in server and 'solution: input.solution' in server, "Captured direct wire rule mismatch")
    require(policy["normalization_applied"] is False and policy["CRLF_count"] == 221 and policy["bare_CR_count"] == 0 and policy["source_has_final_LF"] is True and policy["expected_wire_digest_is_not_observed_website_digest"] is True, "Policy scope mismatch")
    false_keys = [key for key in status if key.endswith("_passed") or key.endswith("_confirmed")] + ["mathematical_dual_kernel_complete", "official_website_result_observed", "upload_ready", "submitted"]
    require(all(status[key] is False for key in false_keys), "V7 status incorrectly claims validation")
    null_keys = ("official_verdict", "actual_original_parent_exit_code", "public_job_id", "public_acceptance_commit")
    require(all(status[key] is None for key in null_keys), "V7 unknown result is not null")
    for packet in (pm, wm, fields, prediction):
        for key in ("upload_ready", "submitted", "official_website_acceptance"):
            if key in packet:
                require(packet[key] is False, "Material claims actual upload or acceptance")
    require(status["historical_v6_evidence_does_not_verify_v7"] is True and status["proof_compiler_export_kernel_network_calls_by_preparer"] == 0, "Historical scope mismatch")
    require(math["v7_mathematical_verification_performed"] is False and math["exact_ratio_identity_rechecked_for_v7"] is False, "Original preparer scope mismatch")
    for row in INPUTS.values():
        data = (ROOT / row["path"]).read_bytes()
        require(len(data) == row["bytes"] and sha(data) == row["sha256"], "Frozen input changed during audit")
    report = {"schema": "w9a2-v7-materials-independent-static-v1", "result": "PASS_STATIC",
              "scope": "Independent bytes, JSON, captured server-source inspection and exact rational metadata arithmetic only. No author script imported/executed; no Lean/compiler/exporter/kernel/network run.",
              "source_sha256": SOURCE_SHA, "source_bytes": len(source), "id": IDENT, "summary_characters": len(summary),
              "author": expected["author"], "model": None, "harness": "Codex", "score": score,
              "server_manifest_bytes": len(encoded), "server_manifest_sha256": sha(encoded), "predicted_bundle_digest": digest,
              "predicted_only_not_observed_submission": True, "current_ID_availability_not_queried": True,
              "prepared_manifest_rows_verified": 13, "wire_manifest_rows_verified": 2, "outer_manifest_rows_verified": 6,
              "source_normalization": "none; 221CRLF and one finalLF retained", "captured_protocol_only_no_fresh_network": True,
              "all_v7_validation_flags_false_and_results_unknown": True, "historical_v6_receipts_not_v7_validation": True,
              "independent_rational_identity_matches_metadata": True, "input_hashes_before_after_identical": True,
              "inputs": list(INPUTS.values()), "proof_execution_count": 0, "network_requests": 0, "frozen_input_writes": 0}
    report_raw = write_new("review.json", report)
    rows = [{"path": "review.json", "bytes": len(report_raw), "sha256": sha(report_raw)},
            {"path": "audit.py", "bytes": Path(__file__).stat().st_size, "sha256": sha(Path(__file__).read_bytes())}]
    manifest_raw = write_new("files.json", {"schema": "independent-static-evidence-files-v1", "files": rows, "proof_execution_count": 0})
    print(json.dumps({"result": "PASS_STATIC", "source_sha256": SOURCE_SHA, "wire_digest": digest,
                      "manifest_sha256": sha(manifest_raw), "inputs": len(INPUTS), "proof_execution_count": 0}))


if __name__ == "__main__":
    main()
