"""Prepared only: fresh DRAFT-v11 metadata/source and PREDICTED wire generator.

Root must separately authorize its one metadata-only execution after freezing/review.
This file never imports old generators, reads live work, or invokes proof/tools/network.
"""
from __future__ import annotations
import argparse
import copy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import time

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
OLD = ROOT / "submission/w9a2-weighted-potential-20261021-prepared-v10"
OLDWIRE = ROOT / "submission/w9a2-weighted-potential-20261021-expected-wire-v10"
DRAFT = ROOT / "research-goal-20261021-w9a2-delivery/draft-v11"
NEW = ROOT / "submission/w9a2-weighted-potential-20261021-prepared-v11"
WIRE = ROOT / "submission/w9a2-weighted-potential-20261021-expected-wire-v11"
SOURCE_BYTES = 1945173
SOURCE_SHA = "a267dd84df81d59e308b220f3b8374fc4c0cc32bea6eaa35db04d846e2b07893"
ID = "lixiang90-w9a2-weighted-potential-v11-20261021"
OLD_ID = "lixiang90-w9a2-weighted-potential-v10-20261021"
SOURCE_COMMIT = "0d67d299ba7f30b0aa32af6efc6b504a9f5371b0"
K = {"numerator": "3337881639516708570682858853672166187793",
     "denominator": "4955348542279967171490000000000000000000"}
INPUTS = {}
DEADLINE = None
WRITTEN_BYTES = 0
WRITTEN_METADATA_BYTES = 0
PINS = {
    "source_manifest": ("research-goal-20261021-w9a2-delivery/draft-v11/files.json", "af6993f5ad3ea281db0b737e52bcc58a8b8670c7be03972ddec8caa94f55246e"),
    "source_contract": ("research-goal-20261021-w9a2-delivery/draft-v11/source-contract.json", "83e96fe4fc090ddcc545c4ed0266e396a3698ad6db1f681f39cb588219e729e9"),
    "source_edits": ("research-goal-20261021-w9a2-targeted-proof-preparation-repair-v1/source-edits.json", "984dfbee7edf7395394290f661fd3df803eeed87022a4ad50e550f9c952182d7"),
    "unique_complete_independent_projection": ("research-goal-20261021-w9a2-v11-projection-independent/files.json", "9754b6269bc0553f9acb3e5e02557bc341e60b407236ec3043665f2b82794da0"),
    "independent_projection_completion": ("research-goal-20261021-w9a2-v11-projection-independent/completion-files.json", "8e776939e8e84fee7c7a0203e6f1083beeb8ced8046a09133d6e6fe13e07127a"),
    "author_targeted_review_not_second_independent": ("research-goal-20261021-w9a2-v11-targeted-formal/files.json", "6f0103af76f32df6b78691ddf828ee118f509a387b6121b80db6136277ffc15a"),
    "public_source_sync": ("research-goal-20261021-w9a2-v11-public-source-sync-v1/files.json", "fa7641a0b8316a286ef40ed73ac194379693c86a04ac84bd3ec8a0e408d740c8"),
    "resource_gate": ("research-goal-20261021-w9a2-v11-resource-gate-v1/resource-gate.json", "47bcd237065069103ae9e21069976710f9b99430a896a4515664bda576cf2f60"),
    "resource_gate_manifest": ("research-goal-20261021-w9a2-v11-resource-gate-v1/files.json", "b5f4f8833863f92ac557bab9ea242cbd808a323e844f9d54a62df465e5680b2f"),
    "resource_runner": ("research-goal-20261021-w9a2-v11-resource-preparation-v1/run_resource.py", "837e24301601a715006bd7b0dcfa9db869385dcb960bbd6624e5931e2eedf75a"),
    "prior_prepared_v10": ("submission/w9a2-weighted-potential-20261021-prepared-v10/files.json", "ab6542f44cd9431ee2122d5271820c0f000faa1fb7ecbb7d19a5776a4fdf1e50"),
    "prior_wire_v10": ("submission/w9a2-weighted-potential-20261021-expected-wire-v10/files.json", "52bce436d97705a7cf41962b0e68d2483103ae82dab3508ed3a44f5ab0256d19"),
    "prior_v10_resource_failure": ("research-goal-20261021-w9a2-v10-resource-failure-v1/files.json", "56ee21b157c35f9418c1c68d4bf20930aa853383131b81c4b02e8c6af2346e67"),
    "initial_v11_producer_parse_failure": ("research-goal-20261021-w9a2-v11-producer-parse-failure-v1/files.json", "a2c97e961bd3a0bd945fc0dc277696b1740ff4b11233db41bde7f2dc4a87cb91"),
}
HISTORICAL_DOCUMENTS = (
    ("LICENSE", "LICENSE", 11558, "1eb85fc97224598dad1852b5d6483bbcf0aa8608790dcc657a5a2a761ae9c8c6"),
    ("ATTRIBUTION.zh.md", "historical-v10/ATTRIBUTION.zh.md", 1993, "a3acbec79cfd0cd2e2f706fc8f26b1cc13e6003624882f184c29b7642325016e"),
    ("MATHEMATICS.zh.md", "historical-v10/MATHEMATICS.zh.md", 3651, "2bbfc627ef14e233b979b00e99c7f4be5d6d600ea346ec64d7127a68cd93f98a"),
    ("mathematical-source-check.json", "historical-v10/mathematical-source-check.json", 2419, "4f0d3cfe70cf74aa9f76e159bcfb8783670bb5831866b7b8fc2b6ab86a91ab19"),
)


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def remaining():
    require(DEADLINE is not None and time.monotonic() <= DEADLINE, "30-second metadata deadline exceeded")


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")


def read(path, expected=None):
    remaining()
    path = path.resolve()
    require(path.is_relative_to(ROOT.resolve()), "Input escapes workspace")
    relative = path.relative_to(ROOT).as_posix()
    require(not relative.startswith("tmp/"), "Live/runtime work reads are forbidden")
    require(path.is_file() and path.stat().st_size <= 2_000_000, "Input missing or exceeds bounded file size")
    raw = path.read_bytes()
    row = {"path": relative, "bytes": len(raw), "sha256": sha(raw)}
    require(expected is None or row["sha256"] == expected, "Pinned input differs: " + relative)
    INPUTS[str(path)] = row
    require(sum(r["bytes"] for r in INPUTS.values()) <= 8_000_000, "Direct input budget exceeded")
    return raw


def pin(path, expected=None):
    read(path, expected)
    return copy.deepcopy(INPUTS[str(path.resolve())])


def load(path, expected=None):
    return json.loads(read(path, expected))


def write_new(path, raw):
    global WRITTEN_BYTES, WRITTEN_METADATA_BYTES
    remaining()
    resolved = path.resolve()
    require(resolved.is_relative_to(NEW.resolve()) or resolved.is_relative_to(WIRE.resolve())
            or resolved == (HERE / "generation-result.json").resolve(), "Write escapes fixed outputs")
    require(not path.exists() and not path.is_symlink(), "Existing output; stop without overwrite/retry")
    WRITTEN_BYTES += len(raw)
    if resolved != (NEW / "proof/Solution.lean").resolve():
        WRITTEN_METADATA_BYTES += len(raw)
    require(WRITTEN_BYTES <= 4_000_000 and WRITTEN_METADATA_BYTES <= 2_000_000, "Output cap exceeded")
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as stream:
        stream.write(raw)
        stream.flush()


def verify_inputs():
    for path, row in INPUTS.items():
        remaining()
        raw = Path(path).read_bytes()
        require(len(raw) == row["bytes"] and sha(raw) == row["sha256"], "Input changed during metadata generation")


def file_manifest(plan, scope):
    return {"schema": "w9a2-v11-DRAFT-material-files-v1", "scope": scope,
        "source_sha256": SOURCE_SHA, "upload_ready": False, "submitted": False,
        "official_website_acceptance": False,
        "files": [{"path": name, "bytes": len(raw), "sha256": sha(raw)} for name, raw in sorted(plan.items())]}


def main():
    global DEADLINE
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root-authorized-metadata-only", action="store_true")
    parser.add_argument("--generator-sha256", required=True)
    parser.add_argument("--preparation-manifest-sha256", required=True)
    args = parser.parse_args()
    require(args.root_authorized_metadata_only, "Root must separately authorize metadata-only execution")
    DEADLINE = time.monotonic() + 30.0
    require(not NEW.exists() and not NEW.is_symlink() and not WIRE.exists() and not WIRE.is_symlink(),
            "Fresh output directories required; no partial completion or retry")
    require(not (HERE / "generation-result.json").exists(), "Metadata generation was already recorded")
    generator = pin(Path(__file__), args.generator_sha256)
    preparation = pin(HERE / "files.json", args.preparation_manifest_sha256)
    start = pin(HERE / "root-resource-start-report.json")
    refs = {key: pin(ROOT / relative, expected) for key, (relative, expected) in PINS.items()}
    source = read(DRAFT / "Solution.lean", SOURCE_SHA)
    require(len(source) == SOURCE_BYTES and len(source) <= 2_000_000, "Wrong source size")
    require(source.count(b"\r\n") == 221 and source.count(b"\r") == 221, "Source newline identity differs")
    contract = load(DRAFT / "source-contract.json", PINS["source_contract"][1])
    summary = contract["summary"]
    require(summary["source_sha256"] == SOURCE_SHA and summary["source_bytes"] == SOURCE_BYTES
            and summary["Graph_row_lemmas"] == 98 and summary["Graph_explicit_bullets"] == 98
            and summary["new_walk_hints"] == 2, "Wrong prepared v11 structural scope")
    require(contract["prepared_only"] is True and contract["Lean_validated"] is False,
            "Prepared contract must not be promoted to a proof receipt")
    source_row = {"path": "proof/Solution.lean", "bytes": SOURCE_BYTES, "sha256": SOURCE_SHA,
                  "copied_without_normalization": True, "CRLF_count": 221,
                  "website_source_limit_bytes": 2_000_000, "source_slack_bytes": 2_000_000 - SOURCE_BYTES}
    original_server = read(OLDWIRE / "expected-server-submission.json",
                           "2d08cb80ca520275d98bc1d3461f71a08021e63031a1f70d25a36082d356962b")
    server = json.loads(original_server)
    require(encoded(server) == original_server and server["id"] == OLD_ID, "Completed v10 server fixture differs")
    require(server["author"] == {"github": "lixiang90", "displayName": "Li Xiang"}
            and server["model"] is None and server["harness"] == "Codex"
            and server["score"] == K and server["license"] == "Apache-2.0", "Identity/ratio/license fields differ")
    require(len(server["summary"]) == 605 and len(server["summary"].encode("utf-16-le")) // 2 == 605,
            "Fixed summary differs")
    require(len(ID) <= 80 and re.fullmatch(r"[a-z0-9][a-z0-9-]*", ID), "ID violates captured contract")
    server["id"] = ID
    server_raw = encoded(server)
    require(server_raw == original_server.replace(OLD_ID.encode(), ID.encode()), "Only server ID may change")
    bundle = sha(b"submission.json\0" + server_raw + b"proof/Solution.lean\0" + source)
    plan = {"proof/Solution.lean": source, "proof/Solution.manifest.json": encoded(source_row)}
    history_documents = []
    for old_name, new_name, expected_bytes, expected_sha in HISTORICAL_DOCUMENTS:
        raw = read(OLD / old_name, expected_sha)
        require(len(raw) == expected_bytes, "Historical document bytes differ")
        plan[new_name] = raw
        history_documents.append({"output": new_name, "source": copy.deepcopy(INPUTS[str((OLD / old_name).resolve())]),
            "copied_byte_exact": True, "scope": "Current license" if new_name == "LICENSE" else "Historical v10 document only, not current v11 source identity or verification"})
    prior_evidence = load(OLD / "evidence-references.json", "1a65b8b86abb6e86eb6d4330cd264c933596b3e41e88002f17919aebd9b08305")
    fields = load(OLD / "website-fields.draft.json", "ff37eb78af54953502f76331c4726f80fbf0021eef2bc664c991c276b673e0ff")
    fields.update({"proposed_id": ID, "suggested_result_name": ID, "proof_file": source_row,
        "identity_source": "Human authorized Li Xiang/lixiang90; no v11 website or session observation by generator",
        "upload_ready": False, "submitted": False, "official_website_acceptance": False})
    require(fields["summary"] == server["summary"] and fields["method"] == server["method"]
            and fields["score"] == K, "Form and server fields differ")
    plan["website-fields.draft.json"] = encoded(fields)
    plan["submission.draft.json"] = server_raw
    policy = load(OLD / "source-wire-policy.json", "6800e47a89f832290152b362baf1abbf4d13f5c3572b128794159506ca1dd2e3")
    policy.update({"source": source_row, "CRLF_count": 221, "bare_CR_count": 0,
        "source_has_final_LF": source.endswith(b"\n"), "normalization_applied": False,
        "scope": "Inherited captured official wire protocol; no fresh client/server/network observation",
        "ID_current_availability_queried": False, "expected_wire_digest_is_not_observed_website_digest": True})
    plan["source-wire-policy.json"] = encoded(policy)
    addendum = (f"当前proof/Solution.lean是冻结draft-v11的原始字节副本：{SOURCE_BYTES}B，SHA256 {SOURCE_SHA}，221处CRLF。"
        f"当前拟用ID为{ID}，署名Li Xiang/GitHub lixiang90，model=null（UI空）、harness Codex；用户既有同一目的/条款授权不在本生成器重新接受或修改。\n\n"
        "当前许可证LICENSE沿用完整v10材料的原始Apache-2.0文件。historical-v10中的ATTRIBUTION、MATHEMATICS和mathematical-source-check三个文件全部原字节保留，"
        "其draft-v10来源、pid、旧source字段和pending措辞仅为历史范围，不能读作v11身份或v11已验证。当前v11身份/范围以本addendum、provenance及verification-status为准。"
        "源码中ajp88、master-of-puppets5/R. Arun Chandru、Samuel Lavery、Kristian Muri Knausgaard、Yuhang Shi、Zero Forge/@zkvoxels等原notice、署名和适用条款均随raw source保留，未改署为当前作者。\n\n"
        "v11在固定v10上新增98个固定u、仍量化所有v的Graph行引理及对应组合，另为r37/r43两个实际失败游走加入两个有界proper-descendant hint，"
        "保持原公开命题、数学数据和比例。此为source-contract及静态投影的准备范围；完整独立反投影只有一份9754b626，completion8e776939说明同一审查完成，author6f0103不是第二份独立审查。"
        "静态反投影、旧rc10 cached-Core开发pilot和所有旧成功/失败均不代替新v11普通Lean检查或独立核。\n\n"
        "完整v11资源构建只引用root给出的历史启动快照：outer95883、parent30160、child18408、t0=43882.609，root启动工具652b70。"
        "本生成器从不查询live work、进程或终态；即使将来生成时root任务已结束，本DRAFT所有v11实际proof/resource/双核/full3200/官网/ready/submitted标志仍为false/unknown。"
        "未来实际结果另封addendum，不回写旧包；本材料不构成上传或法律确认。\n")
    plan["ATTRIBUTION.v11.zh.md"] = addendum.encode("utf-8")
    plan["evidence-references.json"] = encoded({
        "schema": "w9a2-v11-DRAFT-evidence-references-v1", "current_v11_pins": refs,
        "unique_complete_independent_projection_review_count": 1,
        "author_review_is_a_second_independent_review": False,
        "root_reported_historical_resource_start_only": start,
        "v11_actual_resource_terminal_receipt": None, "v11_actual_official_receipt": None,
        "current_source_commit": SOURCE_COMMIT, "public_raw_sync_scope": "One fixed source file only; no current full-tree or ledger audit",
        "historical_failures_and_interruption_from_completed_v10_index": prior_evidence["historical_failures_and_interruption"],
        "historical_rc10_cached_Core_development_pilot_only": prior_evidence["rc10_development_pilot_only"],
        "new_v10_failure_separately_preserved": refs["prior_v10_resource_failure"],
        "historical_documents_scope": history_documents})
    plan["provenance.json"] = encoded({
        "schema": "w9a2-v11-DRAFT-source-provenance-v1", "current_source": source_row,
        "source_origin": INPUTS[str((DRAFT / "Solution.lean").resolve())],
        "source_manifest": refs["source_manifest"], "source_contract": refs["source_contract"],
        "static_source_pins": {k: refs[k] for k in ("source_edits", "unique_complete_independent_projection", "independent_projection_completion", "author_targeted_review_not_second_independent")},
        "fixed_commit": SOURCE_COMMIT, "prior_materials": refs["prior_prepared_v10"],
        "raw_source_copy_without_normalization": True, "embedded_notices_preserved": True,
        "historical_document_copies": history_documents,
        "current_credit_and_scope_document": "ATTRIBUTION.v11.zh.md",
        "model_identifier_not_guessed": True, "old_frozen_files_modified": False,
        "live_work_or_process_queried": False, "runtime_closure_reaudited": False,
        "legal_terms_accepted_or_updated": False, "proof_compiler_export_kernel_network_UI_Git_calls": 0})
    status = {"schema": "w9a2-v11-DRAFT-unverified-status-v1", "source": source_row,
        "prepared_at_UTC": datetime.now(timezone.utc).isoformat(),
        "validation_policy": "All actual v11 proof/resource/dual/full3200/site/ready/submitted flags remain false/unknown; never infer a terminal result from the historical startup capture",
        "compiler_resource_result": "running_at_root_reported_start_only__current_and_terminal_status_unknown",
        "resource_original_start_report": start, "resource_actual_original_outer_exit_code": None,
        "resource_terminal_receipt": None, "official_verdict": None, "public_acceptance_commit": None,
        "prepared_structural_scope": summary,
        "source_static_projection_scope": "One complete independent source projection plus its completion observation; author targeted review is separate non-independent evidence",
        "historical_documents_do_not_verify_v11": True, "historical_start_does_not_claim_current_running": True,
        "live_work_or_process_or_terminal_queried": False, "generator_can_read_future_terminal_receipts": False,
        "future_actual_results_require_separate_hash_linked_addendum": True,
        "current_record_and_quota_rechecked": False, "legal_terms_accepted_or_updated": False,
        "proof_compiler_export_kernel_network_UI_Git_calls": 0}
    for name in ("new_delta_proofs_complete_actual_Lean_passed", "ordinary_modular_complete_actual_Lean_passed",
        "single_file_ordinary_compile_passed", "compiler_C_generation_resource_gate_passed",
        "Comparator_statement_dependency_primitive_passed", "Comparator_transitive_axioms_passed",
        "default_Lean_kernel_replay_passed", "independent_serial_nanoda_passed",
        "mathematical_dual_kernel_complete", "complete_single_3200s_production_passed",
        "official_website_result_observed", "official_website_acceptance_confirmed",
        "public_promotion_confirmed", "upload_ready", "submitted"):
        status[name] = False
    plan["verification-status.json"] = encoded(status)
    readme = (f"DRAFT-v11 only：{ID}；raw source {SOURCE_BYTES}B/{SOURCE_SHA}/221CRLF，Li Xiang/lixiang90、model null、Codex。"
        "K、method、605字符summary及server法律字段沿冻结v10，仅server ID更改。\n\n"
        "当前身份及范围见ATTRIBUTION.v11.zh.md。historical-v10三份原字节数学/归属文档只描述历史v10；LICENSE原字节作当前许可证，原源码第三方notices继续保留。"
        "v11结构为98个Graph行引理及2个新hint；完整独立静审只有一份及其completion，author报告不是第二份。\n\n"
        "root启动95883/parent30160/child18408仅为历史快照，不是当前状态。所有v11实际证明、资源、独立双核、full3200、官网、ready、submitted为false/unknown。"
        "本生成器不读live work/进程/终态；即使外部状态后来变化，本DRAFT也不自动升格。\n\n"
        f"PREDICTED wire bundle：{bundle}；它不是官网实际proofDigest或回执，需独立检查。"
        "仅metadata生成，不调用旧generator/collector、Lean、proof、decoder、compiler、kernel、网络、UI或Git；不接受/修改条款、不上传。后续实际结果另封，不覆盖历史快照。\n")
    plan["README.zh.md"] = readme.encode("utf-8")
    wire_plan = {"expected-server-submission.json": server_raw,
        "prediction.json": encoded({"scope": "PREDICTED v11 DRAFT wire only; independent wire check still required",
            "protocol_basis": "Captured server JSON through complete v10 fixture; only ID changes; no fresh deployment/API observation",
            "submission_id": ID, "source": source_row, "manifest_bytes": len(server_raw),
            "manifest_sha256": sha(server_raw), "expected_job_proofDigest": bundle,
            "algorithm": "SHA256(submission.json + NUL + server manifest UTF8 + proof/Solution.lean + NUL + exact raw source)",
            "official_observed_digest": None, "submitted": False, "upload_ready": False,
            "official_website_acceptance": False})}
    prepared_manifest = encoded(file_manifest(plan, "Fresh v11 DRAFT with historical documents explicitly separated; all v11 actual verification flags false/unknown"))
    wire_manifest = encoded(file_manifest(wire_plan, "PREDICTED wire only, not observed/submitted/ready/accepted"))
    require(len(plan) == 14 and len(wire_plan) == 2, "Unexpected bounded member count")
    planned_bytes = sum(map(len, plan.values())) + sum(map(len, wire_plan.values())) + len(prepared_manifest) + len(wire_manifest)
    require(planned_bytes < 3_900_000 and planned_bytes - len(source) < 1_900_000, "Preflight output budget exceeded")
    verify_inputs()
    NEW.mkdir(parents=True, exist_ok=False)
    WIRE.mkdir(parents=True, exist_ok=False)
    for name, raw in plan.items():
        write_new(NEW / name, raw)
    for name, raw in wire_plan.items():
        write_new(WIRE / name, raw)
    write_new(NEW / "files.json", prepared_manifest)
    write_new(WIRE / "files.json", wire_manifest)
    for directory, outputs in ((NEW, plan), (WIRE, wire_plan)):
        for name, raw in outputs.items():
            remaining()
            require((directory / name).read_bytes() == raw, "Fresh output byte identity differs")
    verify_inputs()
    result = {"schema": "v11-DRAFT-metadata-generation-result-v1", "metadata_only": True,
        "generator": generator, "preparation_manifest": preparation,
        "source": source_row, "ID": ID, "server_manifest_bytes": len(server_raw),
        "server_manifest_sha256": sha(server_raw), "PREDICTED_job_proofDigest": bundle,
        "prepared_manifest": {"path": (NEW / "files.json").relative_to(ROOT).as_posix(), "bytes": len(prepared_manifest), "sha256": sha(prepared_manifest)},
        "wire_manifest": {"path": (WIRE / "files.json").relative_to(ROOT).as_posix(), "bytes": len(wire_manifest), "sha256": sha(wire_manifest)},
        "prepared_members": len(plan), "wire_members": len(wire_plan),
        "all_direct_input_pins_unchanged": True, "source_raw_byte_equal": True,
        "historical_four_documents_byte_equal": True, "input_pins": list(INPUTS.values()),
        "v11_actual_proof_or_resource_PASS_claimed": False, "official_submitted": False,
        "live_work_or_process_or_terminal_queried": False,
        "proof_compiler_export_kernel_network_UI_Git_calls": 0}
    write_new(HERE / "generation-result.json", encoded(result))
    remaining()
    print(json.dumps({k: v for k, v in result.items() if k != "input_pins"}, ensure_ascii=False))


if __name__ == "__main__":
    main()
