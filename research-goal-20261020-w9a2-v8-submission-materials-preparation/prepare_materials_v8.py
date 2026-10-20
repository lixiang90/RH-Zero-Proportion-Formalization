"""Exclusive v8 DRAFT metadata/source copy only; never query the running resource job."""
from __future__ import annotations
import copy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
DRAFT = ROOT / "research-goal-20261020-w9a2-delivery/draft-v8"
REVIEW = ROOT / "research-goal-20261020-w9a2-v8-independent-static"
OLD = ROOT / "submission/w9a2-weighted-potential-20261020-prepared-v7"
OLD_WIRE = ROOT / "submission/w9a2-weighted-potential-20261020-expected-wire-v7"
NEW = ROOT / "submission/w9a2-weighted-potential-20261020-prepared-v8"
NEW_WIRE = ROOT / "submission/w9a2-weighted-potential-20261020-expected-wire-v8"
ID = "lixiang90-w9a2-weighted-potential-v8-20261020"
SOURCE_SHA = "5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b"
DRAFT_SHA = "7f449697314ee04088f1874a6cfdd609c02bb322995feb1197406133ded2a776"
REVIEW_SHA = "dc3adb86ab1c16e4b0ba39135c924c9a01e390b98b8e909dd318bd24d27ceacf"
OLD_SHA = "91c5e7c812e92dddfcf9c4d26fe5061c0fd1d8bb8d50aa69aa29c021cfcc724a"
OLD_WIRE_SHA = "6ea94c6f7d2a02ed64de70a4a349ffa210d61e5a77098aec255aef32cc265a46"
SCHEMA = ROOT / "research-goal-20261020-w9a2-source-normalization-review/source/src/lib/challenge.ts"


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read(path):
    raw = path.read_bytes()
    raw.decode("utf-8", errors="strict")
    return raw


def load(path):
    return json.loads(read(path))


def dump(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def pin(path):
    raw = read(path)
    return {"path": path.relative_to(ROOT).as_posix(), "bytes": len(raw), "sha256": sha(raw)}


def manifest(folder, expected):
    assert sha(read(folder / "files.json")) == expected
    for row in load(folder / "files.json")["files"]:
        path = (folder / row["path"]).resolve()
        assert path.is_relative_to(folder.resolve())
        raw = read(path)
        assert len(raw) == row["bytes"] and sha(raw) == row["sha256"]


def write(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as stream:
        stream.write(raw)


def seal(folder, scope):
    rows = [{"path": path.relative_to(folder).as_posix(), "bytes": len(read(path)), "sha256": sha(read(path))}
            for path in sorted(folder.rglob("*")) if path.is_file()]
    write(folder / "files.json", dump({"schema": "w9a2-prepared-v8-DRAFT-material-files-v1", "scope": scope,
        "source_sha256": SOURCE_SHA, "upload_ready": False, "submitted": False,
        "official_website_acceptance": False, "files": rows}))


def main():
    assert __debug__ and not NEW.exists() and not NEW_WIRE.exists()
    manifest(OLD, OLD_SHA)
    manifest(OLD_WIRE, OLD_WIRE_SHA)
    manifest(DRAFT, DRAFT_SHA)
    manifest(REVIEW, REVIEW_SHA)
    byte_review = load(REVIEW / "byte-review.json")
    assert byte_review["new_sha256"] == SOURCE_SHA and byte_review["new_bytes"] == 1829382
    assert byte_review["all_other_bytes_preserved"] is True and byte_review["exact_edit_count"] == 10
    source = read(DRAFT / "Solution.lean")
    assert len(source) == 1829382 <= 2000000 and sha(source) == SOURCE_SHA
    assert source.count(b"\r\n") == 221 and source.endswith(b"\n")
    assert len(ID) == 45 <= 80 and re.fullmatch(r"[a-z0-9][a-z0-9-]*", ID)
    assert 'id: z.string().max(80).regex(/^[a-z0-9][a-z0-9-]*$/)' in read(SCHEMA).decode()
    submission = copy.deepcopy(load(OLD / "submission.draft.json"))
    assert submission == load(OLD_WIRE / "expected-server-submission.json")
    submission["id"] = ID
    assert submission["model"] is None and submission["harness"] == "Codex"
    assert submission["author"] == {"github": "lixiang90", "displayName": "Li Xiang"}
    assert len(submission["summary"]) == 605 <= 1000
    server = dump(submission)
    assert len(server) == 1343
    digest = sha(b"submission.json\0" + server + b"proof/Solution.lean\0" + source)
    proof = {"path": "proof/Solution.lean", "bytes": len(source), "sha256": SOURCE_SHA,
        "copied_without_normalization": True, "website_source_limit_bytes": 2000000,
        "source_slack_bytes": 2000000 - len(source)}
    start_report = load(HERE / "root-resource-start-report.json")
    assert start_report["original_tool_session"] == 72573 and start_report["parent_pid"] == 12924
    assert start_report["resource_result"] == "pending" and start_report["actual_original_outer_exit_code"] is None
    fields = copy.deepcopy(load(OLD / "website-fields.draft.json"))
    fields.update(proposed_id=ID, suggested_result_name=ID, proof_file=proof,
        upload_ready=False, submitted=False, official_website_acceptance=False)
    fields["identity_source"] = "Human authorized Li Xiang; root reported authenticated GitHub lixiang90. No v8 website action by preparer."
    status = {"schema": "w9a2-prepared-v8-DRAFT-unverified-status-v1", "prepared_at_utc": datetime.now(timezone.utc).isoformat(),
        "source": proof, "validation_policy": "DRAFT only. Root may consider a later upload only after actual resource-gate PASS; no upload decision is encoded here.",
        "ordinary_modular_complete_actual_Lean_passed": False, "single_file_ordinary_compile_passed": False,
        "compiler_C_generation_resource_gate_passed": False, "compiler_resource_result": "pending",
        "resource_original_start_report": pin(HERE / "root-resource-start-report.json"),
        "resource_actual_original_outer_exit_code": None,
        "Comparator_statement_dependency_primitive_passed": False, "Comparator_transitive_axioms_passed": False,
        "default_Lean_kernel_replay_passed": False, "independent_serial_nanoda_passed": False,
        "complete_single_3200s_production_passed": False, "mathematical_dual_kernel_complete": False,
        "official_website_result_observed": False, "official_website_acceptance_confirmed": False,
        "official_verdict": None, "upload_ready": False, "submitted": False,
        "public_job_id": None, "public_acceptance_commit": None,
        "historical_v6_or_v7_evidence_does_not_verify_v8": True,
        "historical_v7_scope": "Exact dae01f source official UI failed with lean-elaboration-failed, while detailed log has seven push_neg warnings and Lean exit137. OOM and a mathematical error were not confirmed. No solution export or kernel completion was observed; this was not a PASS.",
        "historical_v6_scope": "Ordinary Lean and CoreAudit historical partial successes remain restricted to a517. Cold3200 failed; Nano replay interrupted with original outer exit unknown; first official submission timed out.",
        "future_actual_results_require_separate_hash_linked_addendum": True,
        "running_resource_job_queried_by_preparer": False,
        "proof_compiler_export_kernel_network_calls_by_preparer": 0}
    formulas = copy.deepcopy(load(OLD / "mathematical-source-check.json"))
    formulas.update(schema="w9a2-v8-inherited-mathematical-description-v1",
        scope="Inherited mathematical description only; v7-to-v8 static byte review does not verify v8 mathematics",
        historical_description=pin(OLD / "mathematical-source-check.json"))
    formulas.pop("v7_source", None)
    formulas.pop("v7_mathematical_verification_performed", None)
    formulas.pop("exact_ratio_identity_rechecked_for_v7", None)
    formulas.update(v8_source=proof, v8_mathematical_verification_performed=False, exact_ratio_identity_rechecked_for_v8=False)
    references = {"schema": "w9a2-v8-DRAFT-evidence-references-v1", "scope": "Frozen static source plus historical evidence; no v8 validation result",
        "source_draft_manifest": pin(DRAFT / "files.json"), "source_projection": pin(DRAFT / "projection.json"),
        "source_edits": pin(DRAFT / "edits.json"), "independent_static_review_manifest": pin(REVIEW / "files.json"),
        "prior_prepared_v7": pin(OLD / "files.json"), "prior_expected_wire_v7": pin(OLD_WIRE / "files.json"),
        "prior_evidence_links": pin(OLD / "evidence-references.json"),
        "actual_v7_official_failure_archive": pin(ROOT / "research-goal-20261020-w9a2-v7-official-failure-v1/files.json"),
        "root_reported_resource_start_only": pin(HERE / "root-resource-start-report.json"),
        "v8_resource_terminal_receipt": None, "v8_actual_official_receipt": None,
        "source_pushed_commit_reported_by_root": "f2b6d83", "Git_or_network_rechecked_by_preparer": False}
    provenance = {"schema": "w9a2-v8-DRAFT-source-provenance-v1", "source_origin": pin(DRAFT / "Solution.lean"),
        "source_draft_manifest": pin(DRAFT / "files.json"), "independent_static_review_manifest": pin(REVIEW / "files.json"),
        "previous_material_manifest": pin(OLD / "files.json"), "source_copied_without_normalization": True,
        "all_embedded_notices_attributions_licenses_retained_by_static_projection": True,
        "LICENSE_copied_verbatim_from": pin(OLD / "LICENSE"), "ATTRIBUTION_copied_verbatim_from": pin(OLD / "ATTRIBUTION.zh.md"),
        "model_identifier_not_guessed": True, "official_upload_or_acceptance_claimed": False,
        "old_frozen_packages_modified": False, "running_resource_job_queried": False,
        "proof_compiler_export_kernel_network_calls": 0}
    policy = copy.deepcopy(load(OLD / "source-wire-policy.json"))
    policy["source"] = proof
    prediction = {"scope": "Expected new v8 DRAFT manifest/source wire bytes only; no actual submission, resource PASS or mathematical validation",
        "public_main_commit": "1135c0386310a0a038004d3b0fe64d0237e47dce", "submission_id": ID,
        "source": {"path": str(NEW / "proof/Solution.lean"), "bytes": len(source), "sha256": SOURCE_SHA},
        "UI_model_blank_maps_to_server_null": True, "manifest_bytes": len(server), "manifest_sha256": sha(server),
        "expected_job_proofDigest": digest,
        "algorithm": "SHA256(submission.json + NUL + manifest UTF8 + proof/Solution.lean + NUL + exact source bytes)",
        "official_observed_digest": None, "submitted": False, "official_website_acceptance": False}
    note = read(OLD / "MATHEMATICS.zh.md").decode()
    note = note.replace("v7以本次官网实际验证为准；此处仅保留原数学说明。", "v8后续实际验证须另留收据；此处仅保留原数学说明。")
    assert "以上数学说明沿用冻结v6；" in note
    note = note.split("以上数学说明沿用冻结v6；", 1)[0] + "以上数学说明沿用历史冻结材料。v7到v8只为PTT_0..7、PTT、PT十个定义加显式noncomputable，共+140字节；静态独审记录其余源码字节不变。此事实不构成v8编译或内核验证。root报告本次v8资源编译已启动，原session72573/PID12924；本材料不查询它，状态仍pending，不能称通过或上传ready。v7官网实际失败（Lean137，原因未确认）与v6历史成功/超时/中断均不验收新v8。所有后续资源、数学与官网结果须另存实际证据。\n"
    NEW.mkdir(parents=True, exist_ok=False)
    objects = {"proof/Solution.manifest.json": proof, "submission.draft.json": submission,
        "website-fields.draft.json": fields, "verification-status.json": status, "provenance.json": provenance,
        "mathematical-source-check.json": formulas, "evidence-references.json": references, "source-wire-policy.json": policy}
    for name, value in objects.items():
        write(NEW / name, dump(value))
    write(NEW / "proof/Solution.lean", source)
    for name in ("LICENSE", "ATTRIBUTION.zh.md"):
        write(NEW / name, read(OLD / name))
    write(NEW / "MATHEMATICS.zh.md", note.encode())
    write(NEW / "README.zh.md", ("本包是DRAFT：新ID " + ID + "，源码1829382字节、SHA256 " + SOURCE_SHA + "。逐字复制冻结draft-v8，保留221处CRLF及末LF，不改原证明、数据与许可。Li Xiang/lixiang90、605字符summary、method、精确分数、Apache2、model=null（UI空）和harness Codex均同v7。\n\n"
        "所有v8验证flags为false/unknown。root报告唯一资源运行原session72573/PID12924已经启动，本材料只引用该原始启动报告、状态pending，不读取work目录/进程/log/terminal。root只有在以后真实resource PASS后才考虑上传；本包不授予提交或验证执行。旧v7官网失败不是PASS，不适用于v8；旧prepared包与所有source/state/counter保持不变。\n\n"
        "预期wire包只是本地文本预测，不是官网观察；本包未提交、未接受、upload_ready=false。后续真实结果另立hash-linked addendum，不修改本包或Solution字节。\n").encode())
    seal(NEW, "DRAFT v8 source and metadata only; all validation flags false/unknown and resource status pending")
    NEW_WIRE.mkdir(parents=True, exist_ok=False)
    write(NEW_WIRE / "expected-server-submission.json", server)
    write(NEW_WIRE / "prediction.json", dump(prediction))
    seal(NEW_WIRE, "Predicted DRAFT v8 wire digest only; no observed official result or resource PASS")
    manifest(OLD, OLD_SHA)
    manifest(OLD_WIRE, OLD_WIRE_SHA)
    manifest(DRAFT, DRAFT_SHA)
    manifest(REVIEW, REVIEW_SHA)
    assert read(NEW / "proof/Solution.lean") == source
    print(json.dumps({"source_bytes": len(source), "source_sha256": SOURCE_SHA, "submission_id": ID,
        "material_manifest_sha256": sha(read(NEW / "files.json")), "wire_manifest_sha256": sha(read(NEW_WIRE / "files.json")),
        "expected_server_manifest_bytes": len(server), "expected_server_manifest_sha256": sha(server),
        "expected_job_proofDigest": digest, "resource_result": "pending", "upload_ready": False,
        "running_resource_job_queried": False, "proof_compiler_export_kernel_network_calls": 0}), flush=True)


if __name__ == "__main__":
    main()
