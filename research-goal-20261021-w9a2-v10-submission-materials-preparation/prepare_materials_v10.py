"""Generate exclusive DRAFT-v10 source/metadata and PREDICTED wire only.

No old generator/collector, live-work read, proof, compiler, API, network, UI or Git.
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
OLD = ROOT / "submission/w9a2-weighted-potential-20261021-prepared-v9"
OLDWIRE = ROOT / "submission/w9a2-weighted-potential-20261021-expected-wire-v9"
DRAFT = ROOT / "research-goal-20261021-w9a2-delivery/draft-v10"
NEW = ROOT / "submission/w9a2-weighted-potential-20261021-prepared-v10"
WIRE = ROOT / "submission/w9a2-weighted-potential-20261021-expected-wire-v10"
SOURCE_SHA = "86e3f46c90648f98d540d01edd45268d89504b45f7fb9d5d8e53d8582d41e14d"
SOURCE_BYTES = 1914823
ID = "lixiang90-w9a2-weighted-potential-v10-20261021"
OLD_ID = "lixiang90-w9a2-weighted-potential-v9-20261021"
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
    row = {"path": path.relative_to(ROOT).as_posix(), "bytes": len(raw), "sha256": sha(raw)}
    require(expected is None or row["sha256"] == expected, "Input hash differs: " + str(path))
    INPUTS[str(path)] = row
    return raw


def pin(path, expected=None):
    read(path, expected)
    return copy.deepcopy(INPUTS[str(path.resolve())])


def load(path, expected=None):
    return json.loads(read(path, expected))


def write_new(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as stream:
        stream.write(raw)
        stream.flush()


def write_json(path, value):
    write_new(path, encoded(value))


def manifest(directory, scope):
    rows = [{"path": p.relative_to(directory).as_posix(), "bytes": p.stat().st_size,
             "sha256": sha(p.read_bytes())} for p in sorted(directory.rglob("*")) if p.is_file()]
    write_json(directory / "files.json", {
        "schema": "w9a2-prepared-v10-DRAFT-material-files-v1", "scope": scope,
        "source_sha256": SOURCE_SHA, "upload_ready": False, "submitted": False,
        "official_website_acceptance": False, "files": rows})
    path = directory / "files.json"
    return {"path": path.relative_to(ROOT).as_posix(), "bytes": path.stat().st_size,
            "sha256": sha(path.read_bytes())}


def main():
    require(not NEW.exists() and not WIRE.exists(), "Exclusive DRAFT outputs already exist")
    require(not (HERE / "generation-result.json").exists(), "Generation was already recorded")
    pin(Path(__file__))
    now = datetime.now(timezone.utc).isoformat()
    source = read(DRAFT / "Solution.lean", SOURCE_SHA)
    require(len(source) == SOURCE_BYTES and source.count(b"\r\n") == 221, "Wrong source size/newlines")
    require(source.count(b"\r") == 221 and len(source) <= 2000000, "Unexpected CR or source size")
    source_manifest = pin(DRAFT / "files.json")
    contract = load(DRAFT / "source-contract.json", "be66f3a96cb4781c9102d6833844e4e91b2c3dd4152e1dc4633f7475cee8169a")
    contract_pin = copy.deepcopy(INPUTS[str((DRAFT / "source-contract.json").resolve())])
    summary = contract["summary"]
    require(summary["changed_roots"] == 22 and summary["selected_hints"] == 51
            and summary["new_cursor_kernel_lemmas"] == 73
            and summary["source_bytes"] == SOURCE_BYTES and summary["source_sha256"] == SOURCE_SHA,
            "Prepared v10 structural scope differs")
    require(contract["prepared_only"] is True and contract["Lean_validated"] is False,
            "Prepared source contract is not a proof receipt")
    producer = pin(ROOT / "research-goal-20261021-w9a2-all-root-cut-preparation-v1/files.json")
    edits = pin(ROOT / contract["source_edits_path"], "ca45ae3a608f6e0a356df467e5c59f03063ba833cb81dc4da6ea449e8d2eb81b")
    independent = pin(ROOT / "research-goal-20261021-w9a2-v10-projection-independent-math/files.json",
                      "b517317d9b6ea6b3aad954247805988b6e76eb5a0fd1c6709ea7b1de8101968f")
    start = pin(HERE / "root-resource-start-report.json")
    old_manifest = pin(OLD / "files.json", "d3738ae22b53e3f2966885721d3fb6c3c44016528307d4cef02e72916bb15d8d")
    old_wire = pin(OLDWIRE / "files.json", "b2d35fe03c8132852dd42af24ba22e95d44125ac7640ace8487c317efdbd518a")
    original_server = read(OLDWIRE / "expected-server-submission.json",
                           "585adf65bcbd9f401a8a7f19ae9aada99249cbd5afd1d7c80201d5fe5a73debc")
    server = json.loads(original_server)
    require(encoded(server) == original_server and server["id"] == OLD_ID, "Server fixture differs")
    require(server["model"] is None and server["harness"] == "Codex"
            and server["author"] == {"github": "lixiang90", "displayName": "Li Xiang"}, "Wrong author/model/harness")
    require(len(server["summary"]) == 605 and len(server["summary"].encode("utf-16-le")) // 2 == 605,
            "Summary differs")
    require(len(ID) <= 80 and re.fullmatch(r"[a-z0-9][a-z0-9-]*", ID), "Invalid captured-contract ID")
    server["id"] = ID
    server_raw = encoded(server)
    require(server_raw == original_server.replace(OLD_ID.encode(), ID.encode()), "Only server ID may change")
    bundle = sha(b"submission.json\0" + server_raw + b"proof/Solution.lean\0" + source)
    source_row = {"path": "proof/Solution.lean", "bytes": SOURCE_BYTES, "sha256": SOURCE_SHA,
                  "copied_without_normalization": True, "website_source_limit_bytes": 2000000,
                  "source_slack_bytes": 2000000 - SOURCE_BYTES}
    history = {}
    for name, relative in (
        ("v6_cold3200_failure", "research-goal-20261020-w9a2-fullchain-v2-terminal/files.json"),
        ("v6_Nano_interruption_outer_unknown", "research-goal-20261020-w9a2-replay-only-v1-interrupted/files.json"),
        ("v6_first_official_timeout", "research-goal-20261020-w9a2-official-timeout-v1/files.json"),
        ("v7_official_Lean137_failure", "research-goal-20261020-w9a2-v7-official-failure-v1/files.json"),
        ("v8_local_peak_commit_stop", "research-goal-20261020-w9a2-v8-resource-failure-v1/files.json"),
        ("v8_local_interpreter_memory_exception", "research-goal-20261020-w9a2-v8-resource-failure-v2/files.json"),
        ("v8_official_Lean137_failure", "research-goal-20261020-w9a2-v8-official-failure-v1/files.json"),
        ("v9_local_interpreter_memory_exception", "research-goal-20261021-w9a2-v9-resource-failure-v1/files.json"),
    ):
        history[name] = pin(ROOT / relative)
    pilot = pin(ROOT / "research-goal-20261021-w9a2-rc10-five-cut-pilot-pass-v1/files.json",
                "1d81c6031c3687ffaccc73a7f9473b0aa441e571629aa42e0aad593c6387c2aa")
    raw_sync = pin(ROOT / "research-goal-20261021-w9a2-v10-public-source-sync-v1/files.json",
                   "b6658009af52b5a6aba8237dc208ebeb299aa9ded133643597763556315ef924")
    pilot_scope = {"receipt_manifest": pilot, "actual_development_module_pilot_passed": True,
        "scope": "Only six new rc10 cursor proofs with a cached strengthened Core development import; actual original outer0/child0",
        "original_session": 23555, "actual_terminal_tool_chunk": "4c02cb", "child_pid": 50324,
        "terminal_sha256": "08f09bb1c8dfa10b3179878406811292788817f568531108b572beb718e3baa9",
        "complete_v10_source_validated": False, "independent_kernel_passed": False}
    NEW.mkdir(parents=True, exist_ok=False)
    WIRE.mkdir(parents=True, exist_ok=False)
    write_new(NEW / "proof/Solution.lean", source)
    write_json(NEW / "proof/Solution.manifest.json", source_row)
    license_raw = read(OLD / "LICENSE", "1eb85fc97224598dad1852b5d6483bbcf0aa8608790dcc657a5a2a761ae9c8c6")
    write_new(NEW / "LICENSE", license_raw)
    old_attr = read(OLD / "ATTRIBUTION.zh.md").decode("utf-8")
    tail = old_attr[old_attr.index("\n\n本候选沿用"):]
    attr = (f"proof/Solution.lean是冻结draft-v10原始字节的完整副本（{SOURCE_BYTES}字节，SHA256 {SOURCE_SHA}，保留221处CRLF）。"
        "继承draft-v5→v6的wfun全名修复、v6→v7→v8→v9的已冻结代码生成修饰符与诊断删行版本；"
        "v9→v10仅按已冻结source-contract在22个根加入51个cut提示，共73个新游标proof声明。"
        "完整反投影由producer断言，另有且仅有一份完整v10独立静态投影报告；相关索引见evidence-references.json。"
        "rc10六游标开发pilot的实际PASS仅限缓存加强Core的单独模块，不等于完整v10验收。"
        "本材料不重写proof、数据或嵌入署名、版权、LICENSE与NOTICE，不将静态投影视作新Lean或双内核通过。" + tail)
    write_new(NEW / "ATTRIBUTION.zh.md", attr.encode("utf-8"))
    note = read(OLD / "MATHEMATICS.zh.md").decode("utf-8")
    require(note.count("v9后续实际验证须另留收据") == 1, "Historical mathematical note scope differs")
    note = note[:note.index("以上数学说明沿用历史冻结材料。")]
    note = note.replace("v9后续实际验证须另留收据", "v10后续实际验证须另留收据")
    note += ("以上数学说明沿用历史冻结材料，不是v10新数学核查或proof验收。v10准备源在22个根加入51个cut提示，"
        "共73个新游标proof声明；这些是source-contract静态结构计数。producer反投影与唯一完整独立v10静态投影报告均已链接，"
        "不替代Lean正常kernel typechecking或独立内核。rc10六游标开发pilot已实际outer0/child0，但使用缓存加强Core，"
        "不覆盖完整v10。Root仅报告完整v10资源门在启动时运行中（原outer52977、parent51828、child3292）；"
        "本材料未查询活进程、工作目录或终态，不把启动快照当当前状态或PASS。历史v6/v7/v8官网及本地失败、中断与v9本地资源失败均保留，"
        "不被新DRAFT翻为PASS。未来实际完整资源、双核、官网结果须另立证据，不覆盖本快照。\n")
    write_new(NEW / "MATHEMATICS.zh.md", note.encode("utf-8"))
    values = load(OLD / "mathematical-source-check.json")["values_from_historical_v6"]
    write_json(NEW / "mathematical-source-check.json", {
        "schema": "w9a2-v10-inherited-mathematical-description-v1",
        "scope": "Historical formula description only; no numerical or proof replay for v10",
        "values_from_historical_v6": values, "v10_source": source_row,
        "prepared_structural_summary": summary, "complete_v10_independent_static_review": independent,
        "complete_v10_independent_static_review_count": 1, "global_optimality_claimed": False,
        "v10_mathematical_verification_performed": False, "exact_ratio_identity_rechecked_for_v10": False})
    fields = load(OLD / "website-fields.draft.json")
    fields.update({"proposed_id": ID, "suggested_result_name": ID, "proof_file": source_row,
        "identity_source": "Human authorized Li Xiang/lixiang90; no v10 website/session observation or action by preparer",
        "upload_ready": False, "submitted": False, "official_website_acceptance": False})
    require(fields["summary"] == server["summary"] and fields["score"] == server["score"]
            and fields["method"] == server["method"], "Form/server fields differ")
    write_json(NEW / "website-fields.draft.json", fields)
    write_new(NEW / "submission.draft.json", server_raw)
    policy = load(OLD / "source-wire-policy.json")
    policy.update({"source": source_row, "CRLF_count": 221, "bare_CR_count": 0,
        "source_has_final_LF": source.endswith(b"\n"),
        "scope": "Reused captured official client/schema protocol; no fresh deployment observation",
        "normalization_applied": False, "ID_current_availability_queried": False,
        "expected_wire_digest_is_not_observed_website_digest": True})
    write_json(NEW / "source-wire-policy.json", policy)
    write_json(NEW / "evidence-references.json", {
        "schema": "w9a2-v10-DRAFT-evidence-references-v1",
        "scope": "Prepared source/static projection, historical failures, public raw sync, and narrow rc10 development pilot only",
        "source_draft_manifest": source_manifest, "source_contract": contract_pin,
        "source_edits": edits, "producer_preparation_manifest": producer,
        "complete_v10_independent_static_review": independent, "complete_v10_independent_static_review_count": 1,
        "prior_prepared_v9": old_manifest, "prior_expected_wire_v9": old_wire,
        "historical_failures_and_interruption": history, "rc10_development_pilot_only": pilot_scope,
        "fixed_commit_public_raw_sync": raw_sync, "source_commit": "d32802da59804b1b5f3cba0fe4fd5c05d3da4676",
        "root_reported_resource_start_only": start, "v10_complete_resource_terminal_receipt": None,
        "v10_actual_official_receipt": None, "Git_or_network_rechecked_during_material_generation": False})
    write_json(NEW / "provenance.json", {
        "schema": "w9a2-v10-DRAFT-source-provenance-v1", "source_origin": INPUTS[str((DRAFT / "Solution.lean").resolve())],
        "source_draft_manifest": source_manifest, "source_contract": contract_pin,
        "independent_static_review_manifests": [independent], "previous_material_manifest": old_manifest,
        "source_copied_without_normalization": True, "LICENSE_copied_verbatim_from": INPUTS[str((OLD / "LICENSE").resolve())],
        "ATTRIBUTION_tail_preserved_from_v9": INPUTS[str((OLD / "ATTRIBUTION.zh.md").resolve())],
        "embedded_notices_preserved_by_exact_source_copy": True, "model_identifier_not_guessed": True,
        "old_frozen_packages_modified": False, "running_resource_job_or_live_work_queried": False,
        "legal_agreement_or_archive_consent_updated_by_preparer": False,
        "proof_compiler_export_kernel_network_UI_Git_calls_during_generation": 0})
    status = {"schema": "w9a2-prepared-v10-DRAFT-unverified-status-v1", "prepared_at_utc": now, "source": source_row,
        "validation_policy": "DRAFT only; resource RUNNING was reported at startup, no current query or terminal observation; not ready or submitted",
        "compiler_resource_result": "running_at_root_reported_start_only__terminal_unknown",
        "resource_original_start_report": start, "resource_actual_original_outer_exit_code": None,
        "official_verdict": None, "public_job_id": None, "public_acceptance_commit": None,
        "static_projection_scope": "One complete independent PASS_STATIC v10 projection report plus producer reverse assertion; not full proof/resource PASS",
        "prepared_structural_summary": summary, "historical_rc10_development_pilot_only": pilot_scope,
        "historical_evidence_does_not_verify_complete_v10": True,
        "last_known_website_quota": "Previous v8 failure observation had zero remaining; no v10 quota query or claim of a current quota",
        "future_actual_results_require_separate_hash_linked_addendum": True,
        "running_resource_job_or_live_work_queried_by_preparer": False,
        "legal_agreement_or_archive_consent_updated_by_preparer": False,
        "proof_compiler_export_kernel_network_UI_Git_calls_during_generation": 0}
    for name in ("ordinary_modular_complete_actual_Lean_passed", "single_file_ordinary_compile_passed",
        "compiler_C_generation_resource_gate_passed", "Comparator_statement_dependency_primitive_passed",
        "Comparator_transitive_axioms_passed", "default_Lean_kernel_replay_passed", "independent_serial_nanoda_passed",
        "complete_single_3200s_production_passed", "mathematical_dual_kernel_complete", "official_website_result_observed",
        "official_website_acceptance_confirmed", "public_promotion_confirmed", "upload_ready", "submitted"):
        status[name] = False
    write_json(NEW / "verification-status.json", status)
    readme = (f"本包仅为DRAFT-v10：{ID}，Li Xiang/lixiang90，source {SOURCE_BYTES}B / {SOURCE_SHA}，221处CRLF。"
        "原始字节复制冻结draft-v10，保留署名/许可；model=null（UI空）、harness Codex、精确K、method和605字符summary同v9。\n\n"
        "准备结构为22个根/51个cut提示/73个新游标声明；producer反投影与唯一完整独立v10静态投影报告不代表proof PASS。"
        "rc10六游标开发pilot的实际PASS只针对缓存加强Core的单独模块。完整资源状态仅是root提供的启动快照（outer52977、parent51828、child3292），"
        "本生成不读活工作目录或进程，终态未知。所有完整新验证flags false/unknown，未submitted、未ready、未accepted、未promoted。\n\n"
        f"PREDICTED server/source组合digest：{bundle}。它不是官网实际proofDigest或job回执。"
        "历史v6/v7/v8与v9失败/中断完整保全，public raw同步只证明该固定commit单文件相同；没有全树审或新证明验收。"
        "材料生成未运行Lean、数值、compiler、独立kernel、网络、UI或Git，未接受/更新法律条款；actual exit0仅表示metadata生成。未来结果另立addendum。\n")
    write_new(NEW / "README.zh.md", readme.encode("utf-8"))
    require((NEW / "proof/Solution.lean").read_bytes() == source, "Raw source copy differs")
    write_new(WIRE / "expected-server-submission.json", server_raw)
    write_json(WIRE / "prediction.json", {
        "scope": "PREDICTED v10 DRAFT wire bytes only; no observed website digest/submission or complete resource/proof PASS",
        "protocol_basis": "Exact captured server serialization fixture through v9; only ID changes, no fresh deployment observation",
        "submission_id": ID, "source": source_row, "UI_model_blank_maps_to_server_null": True,
        "manifest_bytes": len(server_raw), "manifest_sha256": sha(server_raw), "expected_job_proofDigest": bundle,
        "algorithm": "SHA256(submission.json + NUL + manifest UTF8 + proof/Solution.lean + NUL + exact source bytes)",
        "official_observed_digest": None, "submitted": False, "upload_ready": False, "official_website_acceptance": False})
    prepared_pin = manifest(NEW, "DRAFT v10 exact source and metadata; complete proof/resource/official validation flags false/unknown")
    wire_pin = manifest(WIRE, "PREDICTED wire only; not observed/submitted/ready/accepted")
    for path, row in list(INPUTS.items()):
        require(sha(Path(path).read_bytes()) == row["sha256"], "Input changed during metadata generation")
    result = {"schema": "v10-DRAFT-material-generation-result-v1", "metadata_only": True,
        "source_bytes": SOURCE_BYTES, "source_sha256": SOURCE_SHA, "source_CRLF": 221, "ID": ID,
        "server_manifest_bytes": len(server_raw), "server_manifest_sha256": sha(server_raw),
        "PREDICTED_job_proofDigest": bundle, "prepared_manifest": prepared_pin, "wire_manifest": wire_pin,
        "input_pins": list(INPUTS.values()), "all_input_pins_unchanged": True,
        "source_copy_raw_byte_equal": True, "new_complete_proof_or_resource_PASS_claimed": False,
        "prepared_member_count": len(json.loads((NEW / "files.json").read_bytes())["files"]),
        "wire_member_count": 2, "official_submitted": False,
        "proof_compiler_export_kernel_network_UI_Git_calls_during_generation": 0}
    write_json(HERE / "generation-result.json", result)
    print(json.dumps({k: v for k, v in result.items() if k != "input_pins"}, ensure_ascii=False))


if __name__ == "__main__":
    main()
