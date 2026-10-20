"""One metadata-only independent byte/arithmetic review. No author script import."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import os
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PACKET = ROOT / "submission/w9a2-weighted-potential-20261020-attempt-v8"
EXPECTED = ROOT / "submission/w9a2-weighted-potential-20261020-expected-wire-v8"
SOURCE_SHA = "5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b"
SERVER_SHA = "d88b70050b2a1e1a69d2e1044bcc6a3d1a75c56ab8342f8559f77fe9b270362a"
BUNDLE_SHA = "fb457eecc550ce09bee528294dfff90137631c08e95fa26ffba1e99ec4e11bd4"
raw_inputs = {}

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def sha(value):
    return hashlib.sha256(value).hexdigest()

def read(path):
    value = path.read_bytes()
    if path in raw_inputs:
        require(raw_inputs[path] == value, "Input changed during review")
    raw_inputs[path] = value
    return value

def js(path):
    return json.loads(read(path))

def verify_row(row, base):
    rel = PurePosixPath(row["path"])
    require(not rel.is_absolute() and ".." not in rel.parts, "Unsafe relative member")
    value = read(base.joinpath(*rel.parts))
    require(len(value) == row["bytes"] and sha(value) == row["sha256"], "Member pin mismatch: " + row["path"])
    return value

def verify_manifest(base, expected_sha):
    value = read(base / "files.json")
    require(sha(value) == expected_sha, "Wrong manifest")
    manifest = json.loads(value)
    require(len({row["path"] for row in manifest["files"]}) == len(manifest["files"]), "Duplicate member")
    for row in manifest["files"]:
        verify_row(row, base)
    return manifest

packet = verify_manifest(PACKET, "9d1778957268433a646104108620bfcef2ac999b8630cf378da5d27683e883fa")
expected = verify_manifest(EXPECTED, "7be638eb265f940efaecd305d4a0a8db9d4fedc4cd4c640d974939979eadad25")
require(len(packet["files"]) == 15 and len(expected["files"]) == 2, "Unexpected member counts")
proof = read(PACKET / "proof/Solution.lean")
draft = read(ROOT / "research-goal-20261020-w9a2-delivery/draft-v8/Solution.lean")
require(proof == draft and len(proof) == 1829382 and sha(proof) == SOURCE_SHA, "Raw proof differs")
server_raw = read(PACKET / "submission.draft.json")
server = json.loads(server_raw)
require(server_raw == read(EXPECTED / "expected-server-submission.json"), "Server manifest differs")
require(len(server_raw) == 1343 and sha(server_raw) == SERVER_SHA, "Wrong server bytes")
require(list(server) == ["schemaVersion", "id", "track", "author", "score", "proof", "summary", "method", "model", "harness", "license"], "Server field order")
require(server["id"] == "lixiang90-w9a2-weighted-potential-v8-20261020" and len(server["id"]) <= 80 and re.fullmatch(r"[a-z0-9][a-z0-9-]*", server["id"]), "Wrong ID")
require(server["author"] == {"github": "lixiang90", "displayName": "Li Xiang"}, "Wrong identity")
require(server["model"] is None and server["harness"] == "Codex" and server["license"] == "Apache-2.0", "Wrong model/harness/license")
require(server["score"] == {"numerator": "3337881639516708570682858853672166187793", "denominator": "4955348542279967171490000000000000000000"}, "Wrong p/q")
require(server["track"] == "critical-line" and server["proof"] == {"solution": "proof/Solution.lean", "theorem": "candidate_critical_line_bound", "cumulativeTheorem": "candidate_critical_line_bound_cumulative", "improvementTheorem": "candidate_strict_improvement"}, "Wrong theorem fields")
require(len(server["summary"]) == 605 and len(server["summary"].encode("utf-16-le")) // 2 == 605, "Summary length")
fields = js(PACKET / "website-fields.draft.json")
require(fields["proposed_id"] == server["id"] and fields["public_display_name"] == "Li Xiang" and fields["authenticated_GitHub_login"] == "lixiang90", "UI identity")
require(fields["score"] == server["score"] and fields["summary"] == server["summary"] and fields["method"] == server["method"] and fields["AI_model_optional"] is None and fields["model_field_value"] == "" and fields["coding_harness_optional"] == "Codex", "UI field mismatch")
rebuilt_server = (json.dumps(server, ensure_ascii=False, indent=2) + "\n").encode()
require(rebuilt_server == server_raw, "JSON.stringify(null,2)+LF mismatch")
bundle = sha(b"submission.json\0" + rebuilt_server + b"proof/Solution.lean\0" + proof)
require(bundle == BUNDLE_SHA, "Bundle digest mismatch")
wire = js(PACKET / "expected-wire.json")
require(wire["expected_job_proofDigest"] == bundle and wire["server_manifest_sha256"] == SERVER_SHA and wire["official_observed_digest"] is None, "Wire prediction claims")
policy = js(PACKET / "source-wire-policy.json")
require(policy["normalization_applied"] is False and policy["upload_file_and_avoid_editor_changes"] is True and policy["expected_wire_digest_is_not_observed_website_digest"] is True, "Source policy")
require(proof.count(b"\r\n") == policy["CRLF_count"] == 221 and proof.count(b"\r") - proof.count(b"\r\n") == policy["bare_CR_count"] == 0 and proof.endswith(b"\n") and policy["source_has_final_LF"] is True, "Raw newline policy")
verify_row(policy["captured_policy_manifest"], ROOT)
verify_row(policy["ID_contract_source"], ROOT)
captured_server = read(ROOT / "research-goal-20261020-w9a2-source-normalization-review/source/src/lib/direct-submission.ts")
require(b'JSON.stringify(submission, null, 2)' in captured_server and b'.update("submission.json\\0")' in captured_server and b'.update("proof/Solution.lean\\0")' in captured_server, "Captured protocol missing")
status = js(PACKET / "verification-status.json")
basis = js(PACKET / "official-attempt-basis.json")
verify_row(basis["macro012"], ROOT)
require(basis["macro012"]["sha256"] == "fb7516e57e8fe56802d16b088178c29215d10161a10060a1e007e2b7a9274347", "Macro012 pin")
require(status["local_resource_results"] == "both_recorded_attempts_failed" and status["local_failures"] == basis["local_failures"], "Failure disclosure mismatch")
for name, parent, child, session, exitcode in (("v1", 54132, 12924, 72573, 1), ("v2", 35104, 5564, 93095, 3221226505)):
    failure = status["local_failures"][name]
    for key in ("manifest", "root_outer", "terminal"):
        verify_row(failure[key], ROOT)
    if "stderr" in failure:
        verify_row(failure["stderr"], ROOT)
    actual = js(ROOT / failure["terminal"]["path"])
    require(failure["parent_pid"] == actual["parent_pid"] == parent and failure["child_pid"] == actual["child_pid"] == child and failure["original_outer_session"] == session, "Wrong PID/session roles")
    require(failure["actual_outer_exit_code"] == 1 and failure["actual_child_exit_code"] == actual["actual_child_exit_code"] == exitcode and actual["compiler_resource_gate_passed"] is False, "Failure changed into success")
    outer = js(ROOT / failure["root_outer"]["path"])
    actual_outer = outer.get("actual_original_outer_exit_code", outer.get("actual_original_parent_exit_code"))
    require(actual_outer == 1 and outer["parent_pid"] == parent and outer["child_pid"] == child, "Outer actual roles/exit")
    if name == "v2":
        require(actual["resource_limit_exceeded"] is False and actual["budget_expired_and_owned_child_terminated"] is False and b"memory_exception" in read(ROOT / failure["stderr"]["path"]), "Memory failure scope")
status_false = ["ordinary_modular_complete_actual_Lean_passed", "single_file_ordinary_compile_passed", "compiler_C_generation_resource_gate_passed", "Comparator_statement_dependency_primitive_passed", "Comparator_transitive_axioms_passed", "default_Lean_kernel_replay_passed", "independent_serial_nanoda_passed", "mathematical_dual_kernel_complete", "complete_single_3200s_production_passed", "official_website_result_observed", "official_website_acceptance_confirmed", "submitted", "upload_ready", "old_ready_generator_executed", "new_local_verification_or_memory_increase_performed"]
require(all(status[key] is False for key in status_false) and status["official_verdict"] is None and status["public_job_id"] is None and status["public_acceptance_commit"] is None, "False/unknown status changed")
for document in (packet, fields, wire):
    for key in ("submitted", "upload_ready", "official_website_acceptance", "local_resource_PASS"):
        if key in document:
            require(document[key] is False, "Unexpected success flag")
provenance = js(PACKET / "provenance.json")
require(provenance["actual_v1_roles"] == {"parent": 54132, "child": 12924} and provenance["actual_v2_roles"] == {"parent": 35104, "child": 5564} and provenance["local_or_official_PASS_claimed"] is False, "Corrected provenance roles")
attribution = read(PACKET / "ATTRIBUTION.zh.md").decode()
require(attribution.startswith("proof/Solution.lean是冻结draft-v8原始字节的完整副本") and "draft-v5→v6" in attribution and "Li Xiang" in attribution and "lixiang90" in attribution, "Corrected attribution first sentence")
require(js(PACKET / "mathematical-source-check.json")["v8_mathematical_verification_performed"] is False, "Static math description promoted")
for path, raw in raw_inputs.items():
    require(path.read_bytes() == raw, "Input changed after check")
report = {"schema": "independent-attempt-v8-materials-review-v1", "result": "PASS_METADATA_ONLY", "manifest_members_verified": 15, "expected_wire_members_verified": 2, "source_bytes": len(proof), "source_sha256": SOURCE_SHA, "server_bytes": len(server_raw), "server_sha256": SERVER_SHA, "independently_recomputed_bundle_digest": bundle, "summary_characters_and_UTF16_units": 605, "author": server["author"], "model": None, "harness": "Codex", "score": server["score"], "CRLF_count": 221, "source_normalization_applied": False, "source_equal_frozen_draft_v8": True, "two_actual_local_failures_disclosed_and_bound": True, "corrected_parent_child_roles_verified": True, "corrected_attribution_verified": True, "macro012_bound": basis["macro012"], "all_success_flags_remain_false_or_unknown": True, "all_inputs_unchanged_after_review": True, "scope": "Only Python standard-library byte hashes, JSON structure and string arithmetic. No author generator imported/executed, no Lean/compiler/kernel/export/API/network/process/UI or large runtime tree read. This is a predicted wire and prepared state, not an observed submission or acceptance.", "inputs": [{"path": str(path), "bytes": len(value), "sha256": sha(value)} for path, value in raw_inputs.items()]}
def write_new(path, value):
    with path.open("xb") as stream:
        stream.write(value); stream.flush(); os.fsync(stream.fileno())
def encode(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()
write_new(HERE / "report.json", encode(report))
write_new(HERE / "README.zh.md", ("独立metadata审查通过：attempt-v8的15个成员、expected-wire的2个成员逐一size/SHA一致；rawproof与冻结draft-v8逐字相同。按已捕获server顺序JSON.stringify(null,2)+LF和NUL分隔规则独立重算bundle为fb457eecc550ce09bee528294dfff90137631c08e95fa26ffba1e99ec4e11bd4。\n\nLi Xiang/lixiang90、model null、Codex、605字符summary和p/q一致；221CRLF保留。两次本地失败、真实parent/child角色、归属首句纠正及macro012均核同。所有完整验证/官方接受/已提交成功字段保持false或unknown。\n\n本包只是一轮metadata字节核对，不运行作者脚本或数学验证，不查询API/进程/网络/UI，不声称已上传或官网通过。\n").encode())
files = []
for path in sorted(HERE.iterdir()):
    if path.is_file() and path.name != "files.json":
        value = path.read_bytes()
        files.append({"path": path.name, "bytes": len(value), "sha256": sha(value)})
write_new(HERE / "files.json", encode({"schema": "independent-metadata-review-files-v1", "files": files}))
print(json.dumps({"result": "PASS_METADATA_ONLY", "manifest_sha256": sha((HERE / "files.json").read_bytes()), "report_sha256": sha((HERE / "report.json").read_bytes()), "bundle_digest": bundle, "inputs": len(raw_inputs)}))
