"""Text-only new-source material preparation; no compiler/kernel/network call."""
from __future__ import annotations
import argparse
import copy
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
DRAFT = ROOT / "research-goal-20261020-w9a2-delivery/draft-v6"
OLD = ROOT / "submission/w9a2-weighted-potential-20261020-prepared"
OLD_WIRE = ROOT / "submission/w9a2-weighted-potential-20261020-expected-wire"
NEW = ROOT / "submission/w9a2-weighted-potential-20261020-prepared-v6"
NEW_WIRE = ROOT / "submission/w9a2-weighted-potential-20261020-expected-wire-v6"
OLD_MANIFEST_SHA = "980fb14e136c86fa66294dec2e00c177cd195919a7a7f472352b38fa836c1849"
OLD_WIRE_SHA = "0809d39a37ef2130b502fe6278915d083dee17245292de72b11b16507e1e5960"
EXPECTED_SERVER_MANIFEST_SHA = "e9aace57386e2bbf5ef9db3ad4bb8585db7173b315141b13bee6b1646bd00ec2"
ORDINARY = ROOT / "research-goal-20261020-w9a2-ordinary-v6-terminal"
ORDINARY_SHA = "1553178f354fb05344e73460c5998c42dc06e063354b1f1c25a98d3d5b94ab6c"


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


def manifest(folder, expected):
    assert sha(read(folder / "files.json")) == expected
    data = load(folder / "files.json")
    for row in data["files"]:
        path = (folder / row["path"]).resolve()
        assert path.is_relative_to(folder.resolve())
        raw = read(path)
        assert len(raw) == row["bytes"] and sha(raw) == row["sha256"]
    return data


def write(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as output:
        output.write(raw)


def dump(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def seal(folder, scope, source_sha):
    files = [{"path": path.relative_to(folder).as_posix(), "bytes": path.stat().st_size, "sha256": sha(read(path))}
        for path in sorted(folder.rglob("*")) if path.is_file()]
    write(folder / "files.json", dump({"schema": "w9a2-prepared-v6-material-files-v1", "scope": scope,
        "source_sha256": source_sha, "upload_ready": False, "submitted": False, "official_website_acceptance": False,
        "files": files}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--draft-manifest-sha256", required=True)
    args = parser.parse_args()
    assert __debug__ and not NEW.exists() and not NEW_WIRE.exists()
    manifest(OLD, OLD_MANIFEST_SHA); manifest(OLD_WIRE, OLD_WIRE_SHA)
    manifest(DRAFT, args.draft_manifest_sha256)
    source = read(DRAFT / "Solution.lean")
    plan = load(DRAFT / "candidate-parameters.json")
    assert sha(source) == plan["solution_sha256"] and len(source) == plan["solution_bytes"] <= 2000000
    assert source != read(OLD / "proof/Solution.lean")
    module_dir = DRAFT / "frozen-inputs/StructuralW9A220261020"
    fields = copy.deepcopy(load(OLD / "website-fields.draft.json"))
    submission = copy.deepcopy(load(OLD / "submission.draft.json"))
    submission["model"] = None
    assert submission["score"] == plan["score"] and submission["author"] == {"github": "lixiang90", "displayName": "Li Xiang"}
    assert submission["harness"] == "Codex" and len(submission["summary"]) == 605 <= 1000
    expected_server = read(OLD_WIRE / "expected-server-submission.json")
    assert sha(expected_server) == EXPECTED_SERVER_MANIFEST_SHA
    assert load(OLD_WIRE / "expected-server-submission.json") == submission
    a = 10**20
    c = Fraction(893029029923108825, a) + Fraction(622387738726, 5*a)
    boundary = Fraction(2504722000690, 5*a)
    pressure = Fraction(454741897490, 10**14)
    h = Fraction(6721237468782417141365717707344332375586, 10**40)
    assert (h-pressure)/(1-c) == Fraction(int(plan["score"]["numerator"]), int(plan["score"]["denominator"]))
    assert boundary <= c
    proof = {"path": "proof/Solution.lean", "bytes": len(source), "sha256": sha(source),
        "copied_without_normalization": True, "website_source_limit_bytes": 2000000, "source_slack_bytes": 2000000-len(source)}
    fields.update(proof_file=proof, upload_ready=False, submitted=False, official_website_acceptance=False)
    old_status = load(OLD / "verification-status.json")
    prior_evidence = load(OLD / "evidence-references.json")
    manifest(ORDINARY, ORDINARY_SHA)
    root_observation_path = ROOT / "research-goal-20261020-w9a2-runtime/ordinary-v6-original-exit.json"
    observed = load(root_observation_path)
    attestation = load(ORDINARY / "root-parent-exit-attestation.json")
    assert observed["session"] == attestation["root_observed_parent_session"] == 51666
    assert observed["parent_pid"] == load(ORDINARY / "started.json")["pid"] == 50232
    assert type(observed["actual_original_handle_result"]["exit_code"]) is int and observed["actual_original_handle_result"]["exit_code"] == 0
    assert type(attestation["actual_parent_exit_code"]) is int and attestation["actual_parent_exit_code"] == 0
    assert attestation["terminal_passed"] is True and load(ORDINARY / "terminal.json")["passed"] is True
    assert attestation["fullchain_passed"] is False and attestation["submitted"] is False
    current_roots, current_receipts = {}, []
    for module in ["Counting", "Final"]:
        receipt_path = ORDINARY / ("StructuralW9A220261020_" + module + ".receipt.json")
        log_path = ORDINARY / ("StructuralW9A220261020_" + module + ".log")
        receipt = load(receipt_path)
        assert type(receipt["exit_code"]) is int and receipt["exit_code"] == 0
        assert receipt["ordinary_compile_passed"] is True and receipt["source_unchanged"] is True
        assert receipt["source_sha256"] == sha(read(module_dir / (module + ".lean")))
        assert receipt["log_sha256"] == sha(read(log_path))
        parsed = {name: [item.strip() for item in axioms.split(',') if item.strip()] for name, axioms in
            re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", read(log_path).decode(), re.S)}
        assert parsed == receipt["observed_axioms"]
        assert not set(current_roots).intersection(parsed)
        assert all(set(axioms) <= {"propext", "Quot.sound", "Classical.choice"} for axioms in parsed.values())
        current_roots.update(parsed)
        current_receipts.append({"module": receipt["module"], "source_sha256": receipt["source_sha256"],
            "olean_sha256": receipt["olean_sha256"], "receipt": pin(receipt_path), "log": pin(log_path)})
    assert len(current_roots) == 12
    status = {"schema": "w9a2-prepared-new-source-verification-status-v1", "prepared_at_utc": datetime.now(timezone.utc).isoformat(),
        "source": proof, "ordinary_modular_complete_actual_Lean_passed": True,
        "ordinary_scope": "Actual v6 Counting and unchanged Final PASS, with unchanged earlier Prefix/Core/Graph/Localization development evidence; not a new single-file compile",
        "ordinary_printed_root_count": 12, "ordinary_printed_axioms": current_roots,
        "prior_v5_ordinary_modular_complete_actual_Lean_passed": True,
        "prior_v5_source_sha256": old_status["source"]["sha256"],
        "prior_v5_ordinary_printed_root_count": 12,
        "prior_v5_ordinary_printed_axioms": old_status["ordinary_printed_axioms"],
        "prior_evidence_scope": "The previous exact v5 module sources passed development Lean checks. v5 complete single-file production then exited1 before Comparator/Nano because of ambiguous wfun. New v6 Counting+Final have actual modular PASS; the v6 flat remains unverified.",
        "single_file_ordinary_compile_passed": False, "Comparator_statement_dependency_primitive_passed": False,
        "Comparator_transitive_axioms_passed": False, "default_Lean_kernel_replay_passed": False,
        "independent_serial_nanoda_passed": False, "complete_single_3200s_production_passed": False,
        "official_website_acceptance_confirmed": False, "upload_ready": False, "submitted": False,
        "public_job_id": None, "public_acceptance_commit": None, "old_collector_for_session68653_must_not_be_executed": True,
        "future_results_must_be_separate_hash_linked_addendum": True, "never_edit_frozen_Solution_bytes": True,
        "proof_compiler_export_kernel_network_calls_by_preparer": 0}
    formulas = copy.deepcopy(load(OLD / "mathematical-source-check.json"))
    formulas["scope"] = "Same exact mathematical constants and statements; new source binding only, no new proof/kernel run"
    formulas["module_sources"] = [pin(module_dir / (name + ".lean")) for name in ["Core", "Graph", "Localization", "Counting", "Final"]]
    references = {"schema": "w9a2-prepared-v6-evidence-references-v1", "scope": "Current v6 Counting+Final modular PASS and unchanged earlier modules; v6 production entirely pending",
        "prior_v5_evidence_references": pin(OLD / "evidence-references.json"),
        "prior_v5_actual_modular_receipts": prior_evidence["actual_modular_receipts"],
        "current_v6_modular_receipts": current_receipts, "current_v6_ordinary_archive_manifest": pin(ORDINARY / "files.json"),
        "current_v6_ordinary_root_actual_outer_exit": pin(root_observation_path),
        "current_v6_root_attestation": pin(ORDINARY / "root-parent-exit-attestation.json"),
        "new_draft_manifest": pin(DRAFT / "files.json"), "new_source_review": pin(DRAFT / "source-review.json"),
        "fullrunner_frozen": prior_evidence["fullrunner_frozen"],
        "fresh_record_receipt": None, "actual_complete_production_receipt": None, "official_acceptance_receipt": None}
    provenance = {"schema": "w9a2-prepared-v6-material-source-provenance-v1", "source_origin": pin(DRAFT / "Solution.lean"),
        "source_draft_manifest": pin(DRAFT / "files.json"), "previous_prepared_manifest": pin(OLD / "files.json"),
        "source_copied_without_normalization": True, "all_embedded_notices_attributions_licenses_retained": True,
        "root_project_license_copied_verbatim": pin(ROOT / "LICENSE"), "model_identifier_not_guessed": True,
        "official_record_or_upload_claimed": False, "old_materials_modified": False,
        "proof_compiler_export_kernel_network_calls": 0}
    policy = {"scope": "Current captured deployed client posts original solution state; source must stay raw bytes",
        "source": proof, "CRLF_count": source.count(b"\r\n"), "bare_CR_count": source.count(b"\r")-source.count(b"\r\n"),
        "source_has_final_LF": source.endswith(b"\n"), "normalization_applied": False,
        "captured_policy_manifest": pin(ROOT / "research-goal-20261020-w9a2-source-normalization-review/files.json"),
        "upload_file_and_avoid_editor_changes_then_check_actual_wire_source_bytes": True,
        "predicted_digest_is_not_observed_website_digest": True}
    prediction = {"scope": "Prediction from captured official current schema and unchanged form values; no upload/admission/verification/acceptance",
        "public_main_commit": "1135c0386310a0a038004d3b0fe64d0237e47dce", "source": {"path": str(NEW / "proof/Solution.lean"),
            "bytes": len(source), "sha256": sha(source)}, "UI_model_blank_maps_to_server_null": True,
        "manifest_sha256": EXPECTED_SERVER_MANIFEST_SHA,
        "expected_job_proofDigest": sha(b"submission.json\0" + expected_server + b"proof/Solution.lean\0" + source),
        "algorithm": "SHA256(submission.json + NUL + manifest UTF8 + proof/Solution.lean + NUL + exact source bytes)",
        "official_observed_digest": None, "submitted": False, "official_website_acceptance": False}
    NEW.mkdir(parents=True, exist_ok=False)
    for name, obj in [("proof/Solution.manifest.json", proof), ("submission.draft.json", submission),
        ("website-fields.draft.json", fields), ("verification-status.json", status), ("provenance.json", provenance),
        ("mathematical-source-check.json", formulas), ("evidence-references.json", references), ("source-wire-policy.json", policy)]:
        write(NEW / name, dump(obj))
    write(NEW / "proof/Solution.lean", source)
    write(NEW / "LICENSE", read(ROOT / "LICENSE"))
    write(NEW / "ATTRIBUTION.zh.md", read(OLD / "ATTRIBUTION.zh.md"))
    note = read(OLD / "MATHEMATICS.zh.md").decode()
    note = note.replace("模块化Lean开发已实测通过并仅使用允许的标准公理；", "本次v6 Counting与Final模块化Lean开发已实测通过（12个root均只有标准公理），其余模块保持此前实际通过的原字节；新单文件尚待实际验证；")
    note = note.replace("冻结draft-v5的Final", "冻结draft-v6的Final")
    write(NEW / "MATHEMATICS.zh.md", note.encode())
    write(NEW / "README.zh.md", ("本包绑定新的draft-v6原始源码，比例、公开定理、署名Li Xiang与继承许可证保持原约定。此前v5实际完整单文件生产退出1、尚未进入Comparator/Nano，旧collector不能执行。新Counting+不变Final在原session51666/PID50232实际退出0并有12个标准公理root；新普通单文件、Comparator、defaultLean、serialNano、完整3200秒及官网全部待真实验收。\n\n"
        "UI字段见website-fields.draft.json：模型留空，harness Codex；预期服务端model=null。新source hash/bytes见proof/Solution.manifest.json。新模块化PASS不等于新单文件productionPASS。官网未提交、未接受，upload_ready=false。后续结果须另建hash-linked addendum，不改本包源码。\n").encode())
    seal(NEW, "New v6 source and fields prepared; actual modular PASS only, single-file fullchain and official pending", sha(source))
    NEW_WIRE.mkdir(parents=True, exist_ok=False)
    write(NEW_WIRE / "expected-server-submission.json", expected_server)
    write(NEW_WIRE / "prediction.json", dump(prediction))
    seal(NEW_WIRE, "Expected wire digest for new source only, not an actual submission", sha(source))
    manifest(OLD, OLD_MANIFEST_SHA); manifest(OLD_WIRE, OLD_WIRE_SHA); manifest(DRAFT, args.draft_manifest_sha256); manifest(ORDINARY, ORDINARY_SHA)
    assert read(NEW / "proof/Solution.lean") == source
    print(json.dumps({"source_bytes": len(source), "source_sha256": sha(source),
        "material_manifest_sha256": sha(read(NEW / "files.json")), "wire_manifest_sha256": sha(read(NEW_WIRE / "files.json")),
        "expected_job_proofDigest": prediction["expected_job_proofDigest"], "upload_ready": False,
        "proof_compiler_export_kernel_network_calls": 0}), flush=True)


if __name__ == "__main__":
    main()
