"""Prepare exclusive v7 text packages after frozen independent source review; no proof/network calls."""
from __future__ import annotations
import copy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
DRAFT = ROOT / "research-goal-20261020-w9a2-delivery/draft-v7"
OLD = ROOT / "submission/w9a2-weighted-potential-20261020-prepared-v6"
OLD_WIRE = ROOT / "submission/w9a2-weighted-potential-20261020-expected-wire-v6"
NEW = ROOT / "submission/w9a2-weighted-potential-20261020-prepared-v7"
NEW_WIRE = ROOT / "submission/w9a2-weighted-potential-20261020-expected-wire-v7"
ID = "lixiang90-w9a2-weighted-potential-v7-20261020"
SOURCE_SHA = "dae01f6844642d7f9ee8180616c1f57aefc18ab8616bc8a4a46a14bf8e9fefc6"
DRAFT_SHA = "08844b98778d5197ad39cd6afe0c796f94e1808f04f17a348f18c8f2bd4efab1"
REVIEW_SHA = "3ce7c8654eacc8ed9be327030e6cd824aa869554da3183c549de6945acf5f973"
OLD_SHA = "55c28b9f90515324f40144822d9e84b301fe9001ec1a03e8df2bf1350159522f"
OLD_WIRE_SHA = "f81666062165a2a1e60bd59b88cedcc237e72bebe9faca0f183b021fec636851"
SERVER_SHA = "7d78afb3d25847b89bd0d4daae06daec52e55e8a39524f82431599bbf21d70f6"
SCHEMA = ROOT / "research-goal-20261020-w9a2-source-normalization-review/source/src/lib/challenge.ts"


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read(path):
    raw = path.read_bytes()
    raw.decode("utf-8", errors="strict")
    return raw


def load(path):
    return json.loads(read(path))


def pin(path):
    raw = read(path)
    return {"path": path.relative_to(ROOT).as_posix(), "bytes": len(raw), "sha256": sha(raw)}


def manifest(folder, filename, expected):
    assert sha(read(folder / filename)) == expected
    packet = load(folder / filename)
    for row in packet["files"]:
        path = (folder / row["path"]).resolve()
        assert path.is_relative_to(folder.resolve())
        raw = read(path)
        assert len(raw) == row["bytes"] and sha(raw) == row["sha256"]


def dump(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def write(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as stream:
        stream.write(raw)


def seal(folder, scope):
    rows = [{"path": path.relative_to(folder).as_posix(), "bytes": len(read(path)), "sha256": sha(read(path))}
            for path in sorted(folder.rglob("*")) if path.is_file()]
    write(folder / "files.json", dump({"schema": "w9a2-prepared-v7-material-files-v1", "scope": scope,
        "source_sha256": SOURCE_SHA, "upload_ready": False, "submitted": False,
        "official_website_acceptance": False, "files": rows}))


def main():
    assert __debug__ and not NEW.exists() and not NEW_WIRE.exists()
    manifest(OLD, "files.json", OLD_SHA)
    manifest(OLD_WIRE, "files.json", OLD_WIRE_SHA)
    manifest(DRAFT, "files.json", DRAFT_SHA)
    manifest(HERE, "source-review-files.json", REVIEW_SHA)
    review = load(HERE / "source-review.json")
    assert review["independent_derivation_matches"] is True and review["independent_reverse_projection_matches"] is True
    assert review["source"] == pin(DRAFT / "Solution.lean")
    source = read(DRAFT / "Solution.lean")
    assert len(source) == 1829242 <= 2000000 and sha(source) == SOURCE_SHA
    assert len(ID) == 45 <= 80 and re.fullmatch(r"[a-z0-9][a-z0-9-]*", ID)
    assert 'id: z.string().max(80).regex(/^[a-z0-9][a-z0-9-]*$/)' in read(SCHEMA).decode()
    submission = copy.deepcopy(load(OLD / "submission.draft.json"))
    assert submission == load(OLD_WIRE / "expected-server-submission.json")
    submission["id"] = ID
    assert submission["model"] is None and submission["harness"] == "Codex"
    assert submission["author"] == {"github": "lixiang90", "displayName": "Li Xiang"}
    assert len(submission["summary"]) == 605 <= 1000
    server = dump(submission)
    assert len(server) == 1343 and sha(server) == SERVER_SHA
    digest = sha(b"submission.json\0" + server + b"proof/Solution.lean\0" + source)
    proof = {"path": "proof/Solution.lean", "bytes": len(source), "sha256": SOURCE_SHA,
        "copied_without_normalization": True, "website_source_limit_bytes": 2000000,
        "source_slack_bytes": 2000000 - len(source)}
    fields = copy.deepcopy(load(OLD / "website-fields.draft.json"))
    fields.update(proposed_id=ID, suggested_result_name=ID, proof_file=proof,
        upload_ready=False, submitted=False, official_website_acceptance=False)
    fields["identity_source"] = "Human authorized Li Xiang; root reported authenticated GitHub lixiang90. No v7 website action by preparer."
    status = {"schema": "w9a2-prepared-v7-unverified-status-v1", "prepared_at_utc": datetime.now(timezone.utc).isoformat(),
        "source": proof, "validation_policy": "Official website is the sole v7 validator; no local v7 Lean/exporter/kernel run",
        "ordinary_modular_complete_actual_Lean_passed": False, "single_file_ordinary_compile_passed": False,
        "Comparator_statement_dependency_primitive_passed": False, "Comparator_transitive_axioms_passed": False,
        "default_Lean_kernel_replay_passed": False, "independent_serial_nanoda_passed": False,
        "complete_single_3200s_production_passed": False, "mathematical_dual_kernel_complete": False,
        "official_website_result_observed": False, "official_website_acceptance_confirmed": False,
        "official_verdict": None, "actual_original_parent_exit_code": None,
        "upload_ready": False, "submitted": False, "public_job_id": None, "public_acceptance_commit": None,
        "historical_v6_evidence_does_not_verify_v7": True,
        "historical_v6_scope": "The exact a517 source had actual modular and complete single-file ordinary Lean PASS and two exports; its cold fullchain exceeded 3200 seconds. A separate replay completed CoreAudit/defaultLean, then the Nano process was interrupted with original parent exit unknown. First website submission actually timed out. None of those receipts is a v7 receipt.",
        "future_actual_results_require_separate_hash_linked_addendum": True,
        "proof_compiler_export_kernel_network_calls_by_preparer": 0}
    historical_formulas = load(OLD / "mathematical-source-check.json")
    formula_keys = [key for key in historical_formulas if key not in
                    ("scope", "module_sources", "exact_ratio_identity_checked_with_Fraction", "global_optimality_claimed")]
    formulas = {"schema": "w9a2-v7-inherited-mathematical-description-v1",
        "scope": "Inherited mathematical constants and explanations from frozen v6; no v7 mathematical verification",
        "values_from_historical_v6": {key: historical_formulas[key] for key in formula_keys},
        "historical_description": pin(OLD / "mathematical-source-check.json"),
        "v7_source": proof, "v7_mathematical_verification_performed": False,
        "exact_ratio_identity_rechecked_for_v7": False, "global_optimality_claimed": False}
    references = {"schema": "w9a2-v7-evidence-references-v1", "scope": "Static preparation only; historical evidence stays scoped to v6",
        "source_draft_manifest": pin(DRAFT / "files.json"), "source_projection": pin(DRAFT / "projection.json"),
        "source_edits": pin(DRAFT / "edits.json"), "independent_static_review_manifest": pin(HERE / "source-review-files.json"),
        "historical_prepared_v6": pin(OLD / "files.json"), "historical_expected_wire_v6": pin(OLD_WIRE / "files.json"),
        "historical_cold_timeout": pin(ROOT / "research-goal-20261020-w9a2-fullchain-v2-terminal/files.json"),
        "historical_replay_interruption": pin(ROOT / "research-goal-20261020-w9a2-replay-only-v1-interrupted/files.json"),
        "historical_official_timeout": pin(ROOT / "research-goal-20261020-w9a2-official-timeout-v1/files.json"),
        "v7_local_verification_receipt": None, "v7_actual_official_receipt": None}
    provenance = {"schema": "w9a2-v7-source-provenance-v1", "source_origin": pin(DRAFT / "Solution.lean"),
        "source_draft_manifest": pin(DRAFT / "files.json"), "independent_static_review_manifest": pin(HERE / "source-review-files.json"),
        "previous_material_manifest": pin(OLD / "files.json"), "source_copied_without_normalization": True,
        "all_embedded_notices_attributions_licenses_retained_by_byte_projection": True,
        "LICENSE_copied_verbatim_from": pin(OLD / "LICENSE"), "ATTRIBUTION_copied_verbatim_from": pin(OLD / "ATTRIBUTION.zh.md"),
        "model_identifier_not_guessed": True, "official_upload_or_acceptance_claimed": False,
        "old_frozen_packages_modified": False, "proof_compiler_export_kernel_network_calls": 0}
    policy = {"scope": "Existing captured official client/schema protocol; no new network observation",
        "source": proof, "normalization_applied": False, "CRLF_count": source.count(b"\r\n"),
        "bare_CR_count": source.count(b"\r") - source.count(b"\r\n"), "source_has_final_LF": source.endswith(b"\n"),
        "captured_policy_manifest": pin(ROOT / "research-goal-20261020-w9a2-source-normalization-review/files.json"),
        "ID_contract_source": pin(SCHEMA), "ID_contract_lines_1based": [138, 176],
        "ID_contract": "max80 ASCII lower-case letters/digits/hyphens; first character letter/digit",
        "ID_current_availability_queried": False, "upload_file_and_avoid_editor_changes": True,
        "expected_wire_digest_is_not_observed_website_digest": True}
    prediction = {"scope": "Expected new v7 manifest/source wire bytes only; no actual submission or validation",
        "public_main_commit": "1135c0386310a0a038004d3b0fe64d0237e47dce", "submission_id": ID,
        "source": {"path": str(NEW / "proof/Solution.lean"), "bytes": len(source), "sha256": SOURCE_SHA},
        "UI_model_blank_maps_to_server_null": True, "manifest_bytes": len(server), "manifest_sha256": SERVER_SHA,
        "expected_job_proofDigest": digest,
        "algorithm": "SHA256(submission.json + NUL + manifest UTF8 + proof/Solution.lean + NUL + exact source bytes)",
        "official_observed_digest": None, "submitted": False, "official_website_acceptance": False}
    note = read(OLD / "MATHEMATICS.zh.md").decode()
    note = note.replace("正式production仍须重取当前纪录并生成可信CandidateSpec。", "v7以本次官网实际验证为准；此处仅保留原数学说明。")
    assert "本次v6" in note
    note = note.split("本次v6", 1)[0] + "以上数学说明沿用冻结v6；v7只加8处显式noncomputable并删15行#print诊断。独立静态字节投影保留其余证明、数据、类型与署名，但不构成v7编译或内核验证。v7未运行本地Lean、exporter或kernel，将由官网作为唯一验证器；本包生成时未观察v7提交或官网结果。旧v6普通Lean通过、CoreAudit重放通过、cold3200超时、Nano意外中断与首投官网超时均为历史范围，不能作为v7验收。\n"
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
    write(NEW / "README.zh.md", ("本包为新ID " + ID + " 的v7提交材料快照。源码1829242字节，SHA256 " + SOURCE_SHA + "，逐字复制冻结draft-v7，不做换行或尾空白规范化。署名Li Xiang、GitHub lixiang90，精确分数/summary/method/Apache2许可与v6相同；AI model=null（UI留空），harness Codex。\n\n"
        "新ID符合既有冻结官网80字符/小写字母数字连字符规范；未查询当前服务或ID可用性。源码独审仅证明8处noncomputable与15行诊断删除以外字节保留。全部v7验证标志false/unknown：未运行v7本地Lean/exporter/kernel；本次由官网唯一验证，尚未观察提交或结果。旧v6数学开发与单文件Lean通过、cold3200超时、Nano中断和首投官网超时分别归档，均不验证v7。\n\n"
        "本包upload_ready/submitted/official_acceptance均为false。预期wire摘要位于独立expected-wire-v7包，仅是本地文本预测。后续实际结果另立hash-linked addendum，不修改本包或Solution字节。\n").encode())
    seal(NEW, "Frozen v7 submission preparation only; all v7 validation and official status false/unknown")
    NEW_WIRE.mkdir(parents=True, exist_ok=False)
    write(NEW_WIRE / "expected-server-submission.json", server)
    write(NEW_WIRE / "prediction.json", dump(prediction))
    seal(NEW_WIRE, "Predicted v7 wire digest only; no observed submission or acceptance")
    manifest(OLD, "files.json", OLD_SHA)
    manifest(OLD_WIRE, "files.json", OLD_WIRE_SHA)
    manifest(DRAFT, "files.json", DRAFT_SHA)
    manifest(HERE, "source-review-files.json", REVIEW_SHA)
    assert read(NEW / "proof/Solution.lean") == source
    print(json.dumps({"source_bytes": len(source), "source_sha256": SOURCE_SHA,
        "submission_id": ID, "material_manifest_sha256": sha(read(NEW / "files.json")),
        "wire_manifest_sha256": sha(read(NEW_WIRE / "files.json")), "expected_server_manifest_sha256": SERVER_SHA,
        "expected_job_proofDigest": digest, "v7_verification_passed": False,
        "proof_compiler_export_kernel_network_calls": 0}), flush=True)


if __name__ == "__main__":
    main()
