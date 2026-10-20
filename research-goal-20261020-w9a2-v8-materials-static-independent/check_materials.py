"""Read-only DRAFT metadata audit; does not import either preparation script."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(__file__).resolve().parent
M8 = ROOT / "submission/w9a2-weighted-potential-20261020-prepared-v8"
W8 = ROOT / "submission/w9a2-weighted-potential-20261020-expected-wire-v8"
PREP = ROOT / "research-goal-20261020-w9a2-v8-submission-materials-preparation"
M7 = ROOT / "submission/w9a2-weighted-potential-20261020-prepared-v7"
W7 = ROOT / "submission/w9a2-weighted-potential-20261020-expected-wire-v7"
PRIMARY = ROOT / "research-goal-20261020-w9a2-source-normalization-review/source/src"
SOURCE_SHA = "5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b"
DIGEST = "fb457eecc550ce09bee528294dfff90137631c08e95fa26ffba1e99ec4e11bd4"
inputs = []

def read(p):
    inputs.append(p)
    return p.read_bytes()

def load(p):
    return json.loads(read(p))

def sha(b):
    return hashlib.sha256(b).hexdigest()

def pin(p):
    b = p.read_bytes()
    return {"path": p.relative_to(ROOT).as_posix(), "bytes": len(b), "sha256": sha(b)}

manifests = []
for folder, expected_rows in ((M8, 13), (W8, 2), (PREP, 4)):
    raw = read(folder / "files.json")
    manifest = json.loads(raw)
    assert len(manifest["files"]) == expected_rows
    for row in manifest["files"]:
        p = (folder / row["path"]).resolve()
        assert p.is_relative_to(folder.resolve())
        b = read(p)
        assert len(b) == row["bytes"] and sha(b) == row["sha256"], row
    manifests.append({"path": (folder / "files.json").relative_to(ROOT).as_posix(),
                      "bytes": len(raw), "sha256": sha(raw), "rows_verified": expected_rows})

inputs = list(dict.fromkeys(inputs))
before = {p: pin(p) for p in inputs}
source = read(M8 / "proof/Solution.lean")
assert len(source) == 1829382 and sha(source) == SOURCE_SHA
assert source == read(ROOT / "research-goal-20261020-w9a2-delivery/draft-v8/Solution.lean")
assert source.count(b"\r\n") == source.count(b"\r") == 221
assert len(source) - len(source.rstrip(b"\n")) == 1
assert len(source) < 2000000

draft_raw = read(M8 / "submission.draft.json")
wire_raw = read(W8 / "expected-server-submission.json")
assert draft_raw == wire_raw
m = json.loads(wire_raw)
assert wire_raw == (json.dumps(m, ensure_ascii=False, indent=2) + "\n").encode()
assert len(wire_raw) == 1343 and sha(wire_raw) == "d88b70050b2a1e1a69d2e1044bcc6a3d1a75c56ab8342f8559f77fe9b270362a"
assert m["id"] == "lixiang90-w9a2-weighted-potential-v8-20261020"
assert len(m["id"]) == 45 and re.fullmatch(r"[a-z0-9][a-z0-9-]*", m["id"])
assert m["author"] == {"github": "lixiang90", "displayName": "Li Xiang"}
assert m["model"] is None and m["harness"] == "Codex" and m["license"] == "Apache-2.0"
assert len(m["summary"]) == len(m["summary"].encode("utf-16-le")) // 2 == 605
assert m["summary"].strip() == m["summary"] and m["method"].strip() == m["method"]
assert m["score"] == {
    "numerator": "3337881639516708570682858853672166187793",
    "denominator": "4955348542279967171490000000000000000000"}
assert m["proof"] == {"solution": "proof/Solution.lean", "theorem": "candidate_critical_line_bound",
    "cumulativeTheorem": "candidate_critical_line_bound_cumulative", "improvementTheorem": "candidate_strict_improvement"}
old_manifest = load(W7 / "expected-server-submission.json")
expected_from_old = dict(old_manifest, id=m["id"])
assert expected_from_old == m
for name in ("LICENSE", "ATTRIBUTION.zh.md"):
    assert read(M8 / name) == read(M7 / name)
assert b"Version 2.0, January 2004" in read(M8 / "LICENSE")

fields = load(M8 / "website-fields.draft.json")
assert fields["proposed_id"] == fields["suggested_result_name"] == m["id"]
assert fields["public_display_name"] == m["author"]["displayName"]
assert fields["authenticated_GitHub_login"] == m["author"]["github"]
assert fields["AI_model_optional"] is None and fields["model_field_value"] == ""
assert fields["coding_harness_optional"] == m["harness"]
for key in ("summary", "score", "method"):
    assert fields[key] == m[key]
assert fields["summary_characters"] == fields["summary_utf16_code_units"] == 605

def digest(manifest, body):
    return sha(b"submission.json\0" + manifest + b"proof/Solution.lean\0" + body)

new_digest = digest(wire_raw, source)
assert new_digest == DIGEST
prediction = load(W8 / "prediction.json")
assert prediction["expected_job_proofDigest"] == new_digest
assert prediction["manifest_sha256"] == sha(wire_raw)
old_source = read(M7 / "proof/Solution.lean")
old_wire = read(W7 / "expected-server-submission.json")
old_digest = digest(old_wire, old_source)
v7_observed = load(ROOT / "research-goal-20261020-w9a2-v7-official-submission/root-browser-observation.json")
assert old_digest == v7_observed["actual_UI_proofDigest"] == "1f28020dcda27176a97f8c48e9c9d3f9dc00107ce904f1a1f6706b1f43309771"

server_primary = read(PRIMARY / "lib/direct-submission.ts").decode()
client_primary = read(PRIMARY / "components/direct-submission-form.tsx").decode()
schema_primary = read(PRIMARY / "lib/challenge.ts").decode()
assert '.update("submission.json\\0")' in server_primary and '.update("proof/Solution.lean\\0")' in server_primary
assert 'JSON.stringify(submission, null, 2)' in server_primary
assert 'model: model || null' in client_primary and 'harness: harness || null' in client_primary
assert '          solution,' in client_primary
assert 'summary: z.string().trim().min(20).max(1000)' in schema_primary

prep_obs = load(PREP / "execution-observation.json")
assert prep_obs["actual_metadata_script_exit_code"] == 0
assert prep_obs["material_manifest_sha256"] == manifests[0]["sha256"]
assert prep_obs["wire_manifest_sha256"] == manifests[1]["sha256"]
assert prep_obs["expected_job_proofDigest"] == new_digest
assert prep_obs["expected_server_manifest_sha256"] == sha(wire_raw)
status = load(M8 / "verification-status.json")
assert status["compiler_resource_result"] == "pending"
assert status["resource_actual_original_outer_exit_code"] is None
for obj in (fields, status, prediction, prep_obs):
    assert obj["upload_ready"] is False if "upload_ready" in obj else True
    assert obj["submitted"] is False and obj["official_website_acceptance"] is False if "official_website_acceptance" in obj else obj["submitted"] is False
assert status["compiler_C_generation_resource_gate_passed"] is False
assert status["default_Lean_kernel_replay_passed"] is False
assert status["independent_serial_nanoda_passed"] is False

actual_failure = load(ROOT / "research-goal-20261020-w9a2-v8-resource-failure-v1/root-outer-observation.json")
terminal = load(ROOT / "tmp/w9a2-20261020/v8-resource-v1/terminal.json")
assert actual_failure["original_outer_session_id"] == 72573 and actual_failure["actual_original_outer_exit_code"] == 1
assert actual_failure["parent_pid"] == 54132 and actual_failure["child_pid"] == 12924
assert terminal["compiler_resource_gate_passed"] is False and terminal["resource_limit_exceeded"] is True

attribution = read(M8 / "ATTRIBUTION.zh.md").decode()
assert "proof/Solution.lean是draft-v5原始字节的完整副本" in attribution
start = load(PREP / "root-resource-start-report.json")
assert start["parent_pid"] == actual_failure["child_pid"] != actual_failure["parent_pid"]
findings = [
    {"kind": "stale-source-version-sentence", "path": (M8 / "ATTRIBUTION.zh.md").relative_to(ROOT).as_posix(), "line": 1,
     "actual_text": attribution.splitlines()[0],
     "meaning": "The v8 source is the frozen draft-v8 5424 copy, not a raw draft-v5 copy. License/attribution bytes are preserved from v7, but that inherited version sentence is inaccurate for v8."},
    {"kind": "mislabelled-process-role", "path": (PREP / "root-resource-start-report.json").relative_to(ROOT).as_posix(), "line": 5,
     "field": "parent_pid", "recorded": 12924, "actual_parent_pid": 54132, "actual_child_pid": 12924,
     "meaning": "The historical transcription names the retained Lean child as parent. New current materials must use actual parent/child identities from the terminal evidence."},
    {"kind": "historical-pending-snapshot-not-current-status", "paths": [
        (M8 / "verification-status.json").relative_to(ROOT).as_posix(),
        (M8 / "README.zh.md").relative_to(ROOT).as_posix(),
        (M8 / "MATHEMATICS.zh.md").relative_to(ROOT).as_posix(),
        (M8 / "evidence-references.json").relative_to(ROOT).as_posix(),
        (PREP / "execution-observation.json").relative_to(ROOT).as_posix(),
        (PREP / "root-resource-start-report.json").relative_to(ROOT).as_posix(),
        (PREP / "README.zh.md").relative_to(ROOT).as_posix()],
     "meaning": "These are intentionally immutable preparation/start snapshots. The referenced v1 later terminated with own-runner commit-threshold abort and outer1. Pending/null must not be presented as the current resource result. Root reported v2 not started at task issuance; no v2 PASS is inferred or queried."}
]
inputs = list(dict.fromkeys(inputs))
for p in inputs:
    if p in before:
        assert pin(p) == before[p], p
pins = [pin(p) for p in inputs]
result = {"schema": "w9a2-v8-DRAFT-materials-static-review-v1",
    "result": "BYTE_AND_WIRE_BINDINGS_MATCH_WITH_DOCUMENTED_DRAFT_ACCURACY_FINDINGS",
    "verified_package_manifests": manifests, "source_bytes": len(source), "source_sha256": sha(source),
    "source_equals_frozen_draft_v8": True, "source_CRLF_count": 221, "bare_CR_count": 0, "trailing_LF_count": 1,
    "server_manifest_bytes": len(wire_raw), "server_manifest_sha256": sha(wire_raw),
    "expected_v8_bundle_digest": new_digest, "actual_v8_observed_digest": None,
    "v7_recomputed_digest": old_digest, "matches_existing_root_observed_v7_UI_digest": True,
    "identity_model_harness_pq_summary_license_fields_match": True,
    "license_and_attribution_bytes_equal_v7": True, "findings": findings,
    "current_v1_resource_result": "own-runner threshold abort, actual original outer1; not OS OOM or mathematical rejection",
    "v2_state_scope": "Root task reported not started. No current process/API/status query was performed; no PASS asserted.",
    "upload_ready": False, "submission_authorized_by_this_review": False, "official_acceptance": False,
    "old_frozen_files_modified": False, "proof_math_or_resource_recheck_performed": False,
    "compiler_export_kernel_network_UI_or_process_calls": 0, "main_round_counter_modified": False,
    "input_pins": pins}
(OUT / "review.json").write_text(json.dumps(result, ensure_ascii=True, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"result": result["result"], "manifests": len(manifests), "rows": sum(x["rows_verified"] for x in manifests),
    "source_bytes": len(source), "digest": new_digest, "finding_categories": len(findings), "proof_or_network_runs": 0}))
