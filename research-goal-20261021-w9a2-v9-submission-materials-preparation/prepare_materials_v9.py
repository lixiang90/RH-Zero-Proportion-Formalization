"""Generate exclusive DRAFT-v9 text materials only, with predicted wire bytes.

No Lean import/proof/compiler/AST/runtime/API/network/Git/UI or legacy ready collector.
"""
from __future__ import annotations
import copy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
OLD = ROOT / "submission/w9a2-weighted-potential-20261020-prepared-v8"
OLDWIRE = ROOT / "submission/w9a2-weighted-potential-20261020-expected-wire-v8"
CORRECTED_ATTRIBUTION = ROOT / "submission/w9a2-weighted-potential-20261020-attempt-v8/ATTRIBUTION.zh.md"
DRAFT = ROOT / "research-goal-20261021-w9a2-delivery/draft-v9"
NEW = ROOT / "submission/w9a2-weighted-potential-20261021-prepared-v9"
WIRE = ROOT / "submission/w9a2-weighted-potential-20261021-expected-wire-v9"
SOURCE_SHA = "7552bbb829b86986798b58cf40caf998ea8c51ab19201998b533dae4b9518c99"
SOURCE_BYTES = 1861120
ID = "lixiang90-w9a2-weighted-potential-v9-20261021"
OLD_ID = "lixiang90-w9a2-weighted-potential-v8-20261020"
FORMAL = ROOT / "research-goal-20261021-w9a2-v9-projection-independent-formal/files.json"
MATH = ROOT / "research-goal-20261021-w9a2-v9-projection-independent-math/files.json"
INPUTS = {}


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")


def read(path, expected=None):
    path = path.resolve()
    require(path.is_relative_to(ROOT.resolve()), "Input escapes workspace")
    raw = path.read_bytes()
    pin = {"path": path.relative_to(ROOT).as_posix(), "bytes": len(raw), "sha256": sha(raw)}
    require(expected is None or pin["sha256"] == expected, "Input hash differs: " + str(path))
    INPUTS[str(path)] = pin
    return raw


def pin(path, expected=None):
    read(path, expected)
    return copy.deepcopy(INPUTS[str(path.resolve())])


def load(path):
    return json.loads(read(path))


def write_new(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as stream:
        stream.write(raw)


def write_json(path, value):
    write_new(path, encoded(value))


def manifest(directory, scope):
    rows = []
    for path in sorted(directory.rglob("*")):
        if path.is_file():
            raw = path.read_bytes()
            rows.append({"path": path.relative_to(directory).as_posix(), "bytes": len(raw), "sha256": sha(raw)})
    write_json(directory / "files.json", {
        "schema": "w9a2-prepared-v9-DRAFT-material-files-v1", "scope": scope,
        "source_sha256": SOURCE_SHA, "upload_ready": False, "submitted": False,
        "official_website_acceptance": False, "files": rows})
    return {"path": (directory / "files.json").relative_to(ROOT).as_posix(),
            "bytes": (directory / "files.json").stat().st_size,
            "sha256": sha((directory / "files.json").read_bytes())}


def main():
    require(not NEW.exists() and not WIRE.exists(), "DRAFT outputs already exist; no overwrite/retry")
    require(not (HERE / "generation-result.json").exists(), "Generation was already recorded")
    pin(Path(__file__))
    now = datetime.now(timezone.utc).isoformat()
    source = read(DRAFT / "Solution.lean", SOURCE_SHA)
    require(len(source) == SOURCE_BYTES and len(source) <= 2000000, "Wrong source bytes")
    source_manifest = pin(DRAFT / "files.json", "d5cb77b9915dc7437a66a5739acd57093f0ed6acc6f0643e995f415169f2a454")
    source_projection = pin(DRAFT / "projection.json", "45c9bb21876f96d6427688bf466c8b7128b535dbb9aa0d86e55feae7b2bb5a80")
    formal, math = pin(FORMAL), pin(MATH)
    require(formal["sha256"].startswith("a8decada") and math["sha256"].startswith("1d947e89"), "Wrong source projection reviews")
    start = pin(HERE / "root-resource-start-report.json")
    old_manifest = pin(OLD / "files.json", "5bfb2d54a88cf28dd2b0b5b413bf3e5df5f3967d04d85d4037f93eddf051ca1e")
    old_wire_manifest = pin(OLDWIRE / "files.json", "7be638eb265f940efaecd305d4a0a8db9d4fedc4cd4c640d974939979eadad25")
    original_server = read(OLDWIRE / "expected-server-submission.json", "d88b70050b2a1e1a69d2e1044bcc6a3d1a75c56ab8342f8559f77fe9b270362a")
    server = json.loads(original_server)
    require(encoded(server) == original_server and server["id"] == OLD_ID, "Captured server serialization fixture changed")
    require(server["model"] is None and server["harness"] == "Codex" and server["author"] == {"github": "lixiang90", "displayName": "Li Xiang"}, "Unexpected attribution fields")
    require(len(server["summary"]) == 605 and len(server["summary"].encode("utf-16-le")) // 2 == 605, "Summary changed")
    require(len(ID) <= 80 and re.fullmatch(r"[a-z0-9][a-z0-9-]*", ID), "ID violates captured contract")
    server["id"] = ID
    server_raw = encoded(server)
    require(server_raw == original_server.replace(OLD_ID.encode(), ID.encode()), "Only server ID may change")
    bundle = sha(b"submission.json\0" + server_raw + b"proof/Solution.lean\0" + source)
    source_row = {"path": "proof/Solution.lean", "bytes": len(source), "sha256": SOURCE_SHA,
                  "copied_without_normalization": True, "website_source_limit_bytes": 2000000,
                  "source_slack_bytes": 2000000 - len(source)}
    references = {}
    history = (
        ("v6_cold3200_failure", "research-goal-20261020-w9a2-fullchain-v2-terminal/files.json"),
        ("v6_Nano_interruption_outer_unknown", "research-goal-20261020-w9a2-replay-only-v1-interrupted/files.json"),
        ("v6_first_official_timeout", "research-goal-20261020-w9a2-official-timeout-v1/files.json"),
        ("v7_official_Lean137_failure", "research-goal-20261020-w9a2-v7-official-failure-v1/files.json"),
        ("v8_local_peak_commit_stop", "research-goal-20261020-w9a2-v8-resource-failure-v1/files.json"),
        ("v8_local_interpreter_memory_exception", "research-goal-20261020-w9a2-v8-resource-failure-v2/files.json"),
        ("v8_official_Lean137_failure", "research-goal-20261020-w9a2-v8-official-failure-v1/files.json"),
    )
    for key, relative in history:
        references[key] = pin(ROOT / relative)
    NEW.mkdir(parents=True, exist_ok=False)
    WIRE.mkdir(parents=True, exist_ok=False)
    write_new(NEW / "proof/Solution.lean", source)
    write_json(NEW / "proof/Solution.manifest.json", source_row)
    license_raw = read(OLD / "LICENSE", "1eb85fc97224598dad1852b5d6483bbcf0aa8608790dcc657a5a2a761ae9c8c6")
    write_new(NEW / "LICENSE", license_raw)
    attr = read(CORRECTED_ATTRIBUTION).decode("utf-8")
    tail = attr[attr.index("\n\n本候选沿用"):]
    attribution = (f"proof/Solution.lean是冻结draft-v9原始字节的完整副本（{SOURCE_BYTES}字节，SHA256 {SOURCE_SHA}）。"
        "继承draft-v5→v6的wfun全名修复、v6→v7与v7→v8的已冻结代码生成修饰符/诊断删行版本；"
        "v8→v9的完整字节投影及两份独立静态审查分别链接在evidence-references.json。"
        "本材料不重写proof、数据或嵌入的署名、版权、LICENSE与NOTICE，也不将静态投影视作新编译/内核通过。" + tail)
    write_new(NEW / "ATTRIBUTION.zh.md", attribution.encode("utf-8"))
    note = read(OLD / "MATHEMATICS.zh.md").decode("utf-8")
    require(note.count("v8后续实际验证须另留收据") == 1 and "以上数学说明沿用历史冻结材料。" in note, "Historical math note scope changed")
    note = note.replace("v8后续实际验证须另留收据", "v9后续实际验证须另留收据")
    note = note[:note.index("以上数学说明沿用历史冻结材料。")]
    note += ("以上数学说明沿用历史冻结材料，不是v9新数学核查或proof验收。固定v9相对v8的完整字节投影和两份独立静态审查已链接；"
        "它们不替代Lean正常kernel typechecking、独立内核或官网验收。Root报告资源门在启动时运行中，原outer23402、parent32660、child54436；"
        "本材料不查询该进程或输出，后续终态未知，不称通过或上传ready。v6 cold3200失败/Nano中断/首投timeout、v7官网Lean137失败与v8两次本地资源失败/官网Lean137失败均保全，"
        "不被新v9材料翻为PASS。未来实际资源、数学或官网结果须另立证据，不覆盖本DRAFT。\n")
    write_new(NEW / "MATHEMATICS.zh.md", note.encode("utf-8"))
    math_values = load(OLD / "mathematical-source-check.json")["values_from_historical_v6"]
    write_json(NEW / "mathematical-source-check.json", {
        "schema": "w9a2-v9-inherited-mathematical-description-v1",
        "scope": "Historical formula description only; no numerical or proof replay for v9",
        "values_from_historical_v6": math_values, "v9_source": source_row,
        "static_projection_reviews": [formal, math], "global_optimality_claimed": False,
        "v9_mathematical_verification_performed": False, "exact_ratio_identity_rechecked_for_v9": False})
    fields = load(OLD / "website-fields.draft.json")
    fields.update({"proposed_id": ID, "suggested_result_name": ID, "proof_file": source_row,
        "identity_source": "Human authorized Li Xiang/lixiang90; no v9 website/session observation or action by preparer",
        "upload_ready": False, "submitted": False, "official_website_acceptance": False})
    require(fields["summary"] == server["summary"] and fields["score"] == server["score"] and fields["method"] == server["method"], "Form/server fields differ")
    write_json(NEW / "website-fields.draft.json", fields)
    write_new(NEW / "submission.draft.json", server_raw)
    policy = load(OLD / "source-wire-policy.json")
    policy.update({"source": source_row, "CRLF_count": source.count(b"\r\n"),
        "bare_CR_count": source.count(b"\r") - source.count(b"\r\n"), "source_has_final_LF": source.endswith(b"\n"),
        "scope": "Reused captured official client/schema protocol, not a fresh deployment/network observation",
        "normalization_applied": False, "ID_current_availability_queried": False,
        "expected_wire_digest_is_not_observed_website_digest": True})
    write_json(NEW / "source-wire-policy.json", policy)
    write_json(NEW / "evidence-references.json", {
        "schema": "w9a2-v9-DRAFT-evidence-references-v1", "scope": "Static source projection and historical failures; no v9 validation receipts",
        "source_draft_manifest": source_manifest, "source_full_projection": source_projection,
        "formal_complete_projection_review": formal, "mathematical_complete_projection_review": math,
        "prior_prepared_v8": old_manifest, "prior_expected_wire_v8": old_wire_manifest,
        "historical_failures_and_interruption": references, "root_reported_resource_start_only": start,
        "v9_resource_terminal_receipt": None, "v9_actual_official_receipt": None,
        "source_pushed_commit_observed_by_preparer": None, "Git_or_network_rechecked_by_preparer": False})
    write_json(NEW / "provenance.json", {
        "schema": "w9a2-v9-DRAFT-source-provenance-v1", "source_origin": INPUTS[str((DRAFT / "Solution.lean").resolve())],
        "source_draft_manifest": source_manifest, "source_full_projection": source_projection,
        "independent_static_review_manifests": [formal, math], "previous_material_manifest": old_manifest,
        "source_copied_without_normalization": True, "LICENSE_copied_verbatim_from": INPUTS[str((OLD / "LICENSE").resolve())],
        "ATTRIBUTION_tail_preserved_from_corrected_v8": INPUTS[str(CORRECTED_ATTRIBUTION.resolve())],
        "embedded_notices_preserved_by_exact_source_copy": True, "model_identifier_not_guessed": True,
        "old_frozen_packages_modified": False, "running_resource_job_queried": False,
        "legal_agreement_or_archive_consent_updated_by_preparer": False,
        "proof_compiler_export_kernel_network_calls": 0})
    status = {"schema": "w9a2-prepared-v9-DRAFT-unverified-status-v1", "prepared_at_utc": now, "source": source_row,
        "validation_policy": "DRAFT only; resource running at reported startup, no current query or terminal observation; no upload/ready authorization",
        "compiler_resource_result": "running_at_root_reported_start_only__terminal_unknown",
        "resource_original_start_report": start, "resource_actual_original_outer_exit_code": None,
        "official_verdict": None, "public_job_id": None, "public_acceptance_commit": None,
        "static_projection_scope": "Two complete PASS_STATIC byte-projection reports, not new proof or resource validation",
        "historical_v6_v7_v8_evidence_does_not_verify_v9": True,
        "future_actual_results_require_separate_hash_linked_addendum": True,
        "running_resource_job_queried_by_preparer": False,
        "legal_agreement_or_archive_consent_updated_by_preparer": False,
        "proof_compiler_export_kernel_network_calls_by_preparer": 0}
    for name in ("ordinary_modular_complete_actual_Lean_passed", "single_file_ordinary_compile_passed",
        "compiler_C_generation_resource_gate_passed", "Comparator_statement_dependency_primitive_passed",
        "Comparator_transitive_axioms_passed", "default_Lean_kernel_replay_passed", "independent_serial_nanoda_passed",
        "complete_single_3200s_production_passed", "mathematical_dual_kernel_complete", "official_website_result_observed",
        "official_website_acceptance_confirmed", "public_promotion_confirmed", "upload_ready", "submitted"):
        status[name] = False
    write_json(NEW / "verification-status.json", status)
    readme = (f"本包仅为DRAFT-v9：{ID}，Li Xiang/lixiang90，source {SOURCE_BYTES}B / {SOURCE_SHA}。"
        "逐字节复制冻结draft-v9，保留所有换行和嵌入署名/许可；model=null（UI空）、harness Codex、精确K、method与605字符summary同v8。\n\n"
        "资源状态仅是root报告的启动时运行中（outer23402、parent32660、child54436），本准备不查询活进程、输出或收据。全部新验证flags false/unknown，未submitted、未ready、未accepted、未promoted。"
        "两份静态投影审不替代新Lean正常kernel检查或独立双核，历史v6/v7/v8失败与中断逐项链接保全。\n\n"
        f"本地预期server JSON及组合digest仅为PREDICTED：{bundle}。它不是实际官网观察或新job回执。"
        "没有接受/更新网站法律条款、上传、网络、UI、Git、Lean/数值核查、编译或独立kernel调用；实际exit0只能表示材料生成。未来终态须另立addendum，不覆盖本快照。\n")
    write_new(NEW / "README.zh.md", readme.encode("utf-8"))
    require((NEW / "proof/Solution.lean").read_bytes() == source, "Raw source copy differs")
    write_new(WIRE / "expected-server-submission.json", server_raw)
    write_json(WIRE / "prediction.json", {
        "scope": "PREDICTED v9 DRAFT manifest/source wire bytes only; no actual website submission, resource PASS or proof validation",
        "protocol_basis": "Exact captured v8 server-serialization fixture, only ID changes; no fresh deployment observation",
        "submission_id": ID, "source": source_row, "UI_model_blank_maps_to_server_null": True,
        "manifest_bytes": len(server_raw), "manifest_sha256": sha(server_raw), "expected_job_proofDigest": bundle,
        "algorithm": "SHA256(submission.json + NUL + manifest UTF8 + proof/Solution.lean + NUL + exact source bytes)",
        "official_observed_digest": None, "submitted": False, "upload_ready": False, "official_website_acceptance": False})
    prepared_pin = manifest(NEW, "DRAFT v9 raw source and metadata; all proof/resource/official validation flags false/unknown")
    wire_pin = manifest(WIRE, "PREDICTED wire only, not observed/submitted/ready/accepted")
    for path, row in list(INPUTS.items()):
        require(sha(Path(path).read_bytes()) == row["sha256"], "Input changed during material generation")
    result = {"schema": "v9-DRAFT-material-generation-result-v1", "metadata_only": True,
        "source_bytes": SOURCE_BYTES, "source_sha256": SOURCE_SHA, "ID": ID,
        "server_manifest_bytes": len(server_raw), "server_manifest_sha256": sha(server_raw),
        "PREDICTED_job_proofDigest": bundle, "prepared_manifest": prepared_pin, "wire_manifest": wire_pin,
        "input_pins": list(INPUTS.values()), "all_input_pins_unchanged": True,
        "source_copy_raw_byte_equal": True, "new_proof_or_resource_PASS_claimed": False,
        "prepared_member_count": len(json.loads((NEW / "files.json").read_bytes())["files"]),
        "wire_member_count": 2, "official_submitted": False, "proof_compiler_export_kernel_network_UI_Git_calls": 0}
    write_json(HERE / "generation-result.json", result)
    print(json.dumps({k: v for k, v in result.items() if k != "input_pins"}, ensure_ascii=False))


if __name__ == "__main__":
    main()
