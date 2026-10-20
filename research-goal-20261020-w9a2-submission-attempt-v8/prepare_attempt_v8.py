"""Prepare NEW attempt-v8 metadata after a separately authorized macro012 gate.

Source preparation only: never invoke the old ready generator, a proof process,
an API, a version probe, a browser, a network client or Git.
"""
from __future__ import annotations
import argparse
import copy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OLD = ROOT / "submission/w9a2-weighted-potential-20261020-prepared-v8"
WIRE = ROOT / "submission/w9a2-weighted-potential-20261020-expected-wire-v8"
DRAFT = ROOT / "research-goal-20261020-w9a2-delivery/draft-v8"
NEW = ROOT / "submission/w9a2-weighted-potential-20261020-attempt-v8"
REVIEW = ROOT / "research-goal-20261020-w9a2-v8-materials-static-independent/files.json"
MACRO = ROOT / "research-goal-20261016/macro-reviews/012-20261020.zh.md"
MACRO_SHA = "fb7516e57e8fe56802d16b088178c29215d10161a10060a1e007e2b7a9274347"
FAIL1 = ROOT / "research-goal-20261020-w9a2-v8-resource-failure-v1"
FAIL2 = ROOT / "research-goal-20261020-w9a2-v8-resource-failure-v2"
SOURCE_SHA = "5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b"
SERVER_SHA = "d88b70050b2a1e1a69d2e1044bcc6a3d1a75c56ab8342f8559f77fe9b270362a"
WIRE_SHA = "fb457eecc550ce09bee528294dfff90137631c08e95fa26ffba1e99ec4e11bd4"
REVIEW_SHA = "36338e03f7b4244bfab594498d1e97bba076b484fdb0fcb3f42827860edb4ff2"
FAIL1_SHA = "8317a845b841313d4042ae0664a9d38039e96fe05adedee868355636a13a0cf1"
FAIL2_SHA = "31913deddce2ab5ebd5d4efd27d80102c64a54423334095489f13f7589ab2942"
BASIS = "human-authorized official attempt with known local failures; no local PASS"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def load(path):
    return json.loads(path.read_bytes())


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def write_new(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as stream:
        stream.write(raw)


class Preparation:
    def __init__(self, args):
        self.args = args
        self.inputs = {}

    def path(self, value):
        require(isinstance(value, str) and value, "Missing workspace evidence path")
        path = Path(value)
        path = (path if path.is_absolute() else ROOT / path).resolve()
        require(path.is_relative_to(ROOT.resolve()), "Evidence path escaped workspace")
        return path

    def pin(self, path, expected=None, size=None):
        digest, length = hashlib.sha256(), 0
        with path.open("rb") as stream:
            while block := stream.read(1024 * 1024):
                digest.update(block)
                length += len(block)
        row = {"path": path.relative_to(ROOT).as_posix(), "bytes": length, "sha256": digest.hexdigest()}
        if expected is not None:
            require(row["sha256"] == expected, "Hash mismatch: " + str(path))
        if size is not None:
            require(length == size, "Byte-size mismatch: " + str(path))
        self.inputs[str(path)] = row
        return row

    def row(self, row):
        require(isinstance(row, dict) and isinstance(row.get("sha256"), str)
                and len(row["sha256"]) == 64, "Exact nonempty evidence SHA256 required")
        path = self.path(row.get("path"))
        self.pin(path, row["sha256"], row.get("bytes"))
        return path

    def manifest(self, path, expected):
        self.pin(path, expected)
        members = set()
        for row in load(path)["files"]:
            member = (path.parent / row["path"]).resolve()
            require(member.is_relative_to(path.parent.resolve()) and member not in members,
                    "Manifest member escaped or duplicated")
            self.pin(member, row["sha256"], row["bytes"])
            members.add(member)

    def immutable(self):
        for path, row in list(self.inputs.items()):
            self.pin(Path(path), row["sha256"], row["bytes"])

    def validate(self):
        require(__debug__, "Optimized Python unsupported")
        gate_path = self.path(self.args.gate)
        self.pin(gate_path, self.args.gate_sha256)
        gate = load(gate_path)
        require(gate.get("schema") == "w9a2-submission-attempt-v8-gate-v1", "Wrong attempt gate schema")
        require(gate.get("allow_attempt_material_generation") is True and gate.get("proposal_only") is False,
                "Disabled proposal is not authorization")
        require(gate.get("sole_owner") == "/root" and gate.get("basis") == BASIS,
                "Explicit root attempt basis is required; local PASS is not the basis")
        require(isinstance(gate.get("generator_sha256"), str) and len(gate["generator_sha256"]) == 64,
                "Missing exact generator pin")
        self.pin(Path(__file__).resolve(), gate["generator_sha256"])
        require(self.path(gate["output_directory"]) == NEW.resolve() and not NEW.exists(),
                "New attempt output already exists or path changed")
        require(self.row(gate["macro_review_012"]) == MACRO.resolve()
                and gate["macro_review_012"]["sha256"] == MACRO_SHA, "Exact frozen macro012 pin required")
        require(self.row(gate["DRAFT_materials_independent_review"]) == REVIEW.resolve()
                and gate["DRAFT_materials_independent_review"]["sha256"] == REVIEW_SHA, "Wrong DRAFT review pin")
        for row_name, folder, digest in (("local_failure_v1_manifest", FAIL1, FAIL1_SHA),
                                         ("local_failure_v2_manifest", FAIL2, FAIL2_SHA)):
            require(self.row(gate[row_name]) == (folder / "files.json").resolve()
                    and gate[row_name]["sha256"] == digest, "Wrong actual local-failure archive")
            self.manifest(folder / "files.json", digest)
        self.manifest(REVIEW, REVIEW_SHA)
        self.manifest(OLD / "files.json", "5bfb2d54a88cf28dd2b0b5b413bf3e5df5f3967d04d85d4037f93eddf051ca1e")
        self.manifest(WIRE / "files.json", "7be638eb265f940efaecd305d4a0a8db9d4fedc4cd4c640d974939979eadad25")
        self.manifest(DRAFT / "files.json", "7f449697314ee04088f1874a6cfdd609c02bb322995feb1197406133ded2a776")
        v1o, v1t = load(FAIL1 / "root-outer-observation.json"), load(FAIL1 / "job/terminal.json")
        require(v1o["original_outer_session_id"] == 72573 and type(v1o["actual_original_outer_exit_code"]) is int
                and v1o["actual_original_outer_exit_code"] == 1 and v1o["parent_pid"] == 54132
                and v1o["child_pid"] == 12924, "Historical v1 failure roles/outer result changed")
        require(v1t["actual_child_exit_code"] == 1 and v1t["resource_limit_exceeded"] is True
                and v1t["budget_expired_and_owned_child_terminated"] is False
                and v1t["compiler_resource_gate_passed"] is False, "v1 must remain actual commit-stop failure")
        v2o, v2t = load(FAIL2 / "root-outer-observation.json"), load(FAIL2 / "job/terminal.json")
        require(v2o["schema"] == "w9a2-v8-resource-root-outer-observation-v1" and v2o["role"] == "v8-resource-v2"
                and v2o["original_tool_session"] == 93095 and v2o["parent_pid"] == 35104
                and v2o["child_pid"] == 5564 and type(v2o["actual_original_parent_exit_code"]) is int
                and v2o["actual_original_parent_exit_code"] == 1, "RSS attempt must remain actual original outer1")
        require(v2o["actual_original_handle_result"]["exit_code"] == 1
                and v2o["actual_original_handle_result"]["chunk_id"] == "4bb34b", "Missing original failure tool result")
        require(v2t["actual_child_exit_code"] == 3221226505 and v2t["compiler_resource_gate_passed"] is False
                and v2t["candidate_compile_and_C_generation_completed"] is False
                and v2t["resource_limit_exceeded"] is False
                and v2t["budget_expired_and_owned_child_terminated"] is False, "Wrong RSS-attempt failure classification")
        stderr = (FAIL2 / "job/stderr.log").read_bytes()
        require(len(stderr) == 196 and b"lean::memory_exception: excessive memory consumption detected at 'interpreter'" in stderr,
                "Actual archived Lean memory exception must be retained")
        source = (DRAFT / "Solution.lean").read_bytes()
        server = (WIRE / "expected-server-submission.json").read_bytes()
        require(len(source) == 1829382 and sha(source) == SOURCE_SHA
                and source == (OLD / "proof/Solution.lean").read_bytes(), "Exact v8 raw source changed")
        require(len(server) == 1343 and sha(server) == SERVER_SHA
                and server == (OLD / "submission.draft.json").read_bytes(), "Exact form server JSON changed")
        require(sha(b"submission.json\0" + server + b"proof/Solution.lean\0" + source) == WIRE_SHA,
                "Expected v8 wire digest changed")
        metadata = json.loads(server)
        require(metadata["author"] == {"github": "lixiang90", "displayName": "Li Xiang"}
                and metadata["model"] is None and metadata["harness"] == "Codex"
                and len(metadata["summary"]) == 605, "Author/model/harness/summary changed")
        self.source, self.server = source, server
        self.failures = {
            "v1": {"manifest": self.pin(FAIL1 / "files.json"), "root_outer": self.pin(FAIL1 / "root-outer-observation.json"),
                "terminal": self.pin(FAIL1 / "job/terminal.json"), "original_outer_session": 72573,
                "parent_pid": 54132, "child_pid": 12924, "actual_outer_exit_code": 1, "actual_child_exit_code": 1,
                "result": "Own runner stopped at old peak-commit threshold; not OS OOM or mathematics rejection"},
            "v2": {"manifest": self.pin(FAIL2 / "files.json"), "root_outer": self.pin(FAIL2 / "root-outer-observation.json"),
                "terminal": self.pin(FAIL2 / "job/terminal.json"), "stderr": self.pin(FAIL2 / "job/stderr.log"),
                "original_outer_session": 93095, "parent_pid": 35104, "child_pid": 5564,
                "actual_outer_exit_code": 1, "actual_child_exit_code": 3221226505, "actual_child_exit_hex": "0xC0000409",
                "result": "Lean memory_exception at interpreter under local -M6500; no RSS-runner stop or timeout; OS OOM/math rejection not confirmed"}}
        self.basis = {"schema": "w9a2-official-attempt-v8-basis-v1", "basis": BASIS,
            "macro012": self.pin(MACRO), "DRAFT_independent_review": self.pin(REVIEW),
            "authorization_source": "Human previously instructed not to repeat checks and to submit an attempt; root reconciled known local failures and selected the official attempt in macro012",
            "selected_action": "Try fixed v8 in the official unmodified 8GB/3200-second complete verifier after separate root UI action",
            "local_failures": self.failures, "local_resource_PASS_claimed": False,
            "local_math_fullchain_PASS_claimed": False, "local_repeat_or_memory_limit_raise_performed": False,
            "old_ready_generator_called": False, "InfoTree_or_proof_source_modified": False,
            "official_submission_performed_by_generator": False}
        self.immutable()

    def generate(self):
        require(not NEW.exists(), "Exclusive attempt package already exists")
        proof = copy.deepcopy(load(OLD / "proof/Solution.manifest.json"))
        status = {"schema": "w9a2-attempt-v8-known-local-failures-status-v1", "prepared_at_UTC": datetime.now(timezone.utc).isoformat(),
            "source": proof, "basis": BASIS, "local_resource_results": "both_recorded_attempts_failed",
            "local_failures": self.failures, "old_pending_is_historical_snapshot_only": True,
            "ordinary_modular_complete_actual_Lean_passed": False, "single_file_ordinary_compile_passed": False,
            "compiler_C_generation_resource_gate_passed": False, "Comparator_statement_dependency_primitive_passed": False,
            "Comparator_transitive_axioms_passed": False, "default_Lean_kernel_replay_passed": False,
            "independent_serial_nanoda_passed": False, "mathematical_dual_kernel_complete": False,
            "complete_single_3200s_production_passed": False, "official_website_result_observed": False,
            "official_website_acceptance_confirmed": False, "official_verdict": None,
            "submitted": False, "upload_ready": False, "public_job_id": None, "public_acceptance_commit": None,
            "official_attempt_scope": "Human-authorized try with known local soft6500 failure; the official original full verifier decides, and no local PASS is implied",
            "old_ready_generator_executed": False, "new_local_verification_or_memory_increase_performed": False,
            "future_actual_official_results_require_separate_addendum": True,
            "proof_compiler_export_kernel_API_process_network_UI_Git_calls_by_generator": 0}
        fields = copy.deepcopy(load(OLD / "website-fields.draft.json"))
        fields.update(upload_ready=False, submitted=False, official_website_acceptance=False)
        references = {"schema": "w9a2-attempt-v8-evidence-references-v1", "official_attempt_basis": self.basis,
            "source_draft_manifest": self.pin(DRAFT / "files.json"), "historical_DRAFT_materials": self.pin(OLD / "files.json"),
            "DRAFT_findings_review": self.pin(REVIEW), "local_actual_failures": self.failures,
            "exact_unchanged_expected_wire_package": self.pin(WIRE / "files.json"),
            "expected_wire_digest": WIRE_SHA, "actual_official_observed_digest": None, "official_receipt": None}
        provenance = {"schema": "w9a2-attempt-v8-source-provenance-v1", "source": self.pin(DRAFT / "Solution.lean"),
            "source_copied_without_normalization": True, "source_CRLF_count": self.source.count(b"\r\n"),
            "source_final_LF": self.source.endswith(b"\n"), "all_embedded_notices_and_LICENSE_retained": True,
            "ATTRIBUTION_first_sentence_corrected_only_in_new_attempt_package": True,
            "actual_v1_roles": {"parent": 54132, "child": 12924}, "actual_v2_roles": {"parent": 35104, "child": 5564},
            "old_wrong_PID_and_pending_reports_preserved_as_history_not_current_facts": True,
            "old_packages_generators_sources_state_counter_modified": False,
            "local_or_official_PASS_claimed": False}
        attribution = (OLD / "ATTRIBUTION.zh.md").read_bytes()
        old_sentence = "proof/Solution.lean是draft-v5原始字节的完整副本。".encode()
        require(attribution.startswith(old_sentence) and attribution.count(old_sentence) == 1, "Unexpected attribution baseline")
        replacement = ("proof/Solution.lean是冻结draft-v8原始字节的完整副本（1829382字节，SHA256 " + SOURCE_SHA + "）。"
            "该源沿draft-v5→v6（3处wfun全名）、v6→v7（8处显式noncomputable并删15行#print诊断）、v7→v8（PTT_0..7、PTT、PT共10处显式noncomputable）继承，逐版精确差分与旧证据保全。").encode()
        attribution = replacement + attribution[len(old_sentence):]
        note = (OLD / "MATHEMATICS.zh.md").read_text(encoding="utf-8")
        require("以上数学说明沿用历史冻结材料。" in note, "Unexpected inherited note")
        note = note.split("以上数学说明沿用历史冻结材料。", 1)[0] + "以上为固定v8源码中的数学内容与历史说明，不构成本地v8通过。两次本地资源门实际失败：v1由旧commit线停止；RSS-only v2原93095/parent35104/child5564实际outer1，stderr为Lean memory_exception at interpreter，未完成C生成。旧pending和历史成功只属各自源码/时点，不验收v8。用户授权不再重复核查而带已知local soft6500失败去官网尝试；root按macro012选择官方原8GB/3200完整验收，不提高本地-M、不改InfoTree或证明源。官网双核、完整流水线与接受尚未完成，尚未上传；官网实际结果须另留收据。\n"
        prediction = {"scope": "Unchanged expected wire bytes for human-authorized official attempt with disclosed local failures; no observed upload or acceptance",
            "source": proof, "server_manifest_sha256": SERVER_SHA, "expected_job_proofDigest": WIRE_SHA,
            "algorithm": "SHA256(submission.json + NUL + exact server JSON + proof/Solution.lean + NUL + exact source bytes)",
            "official_observed_digest": None, "submitted": False, "official_website_acceptance": False}
        NEW.mkdir(parents=True, exist_ok=False)
        for name, raw in (("proof/Solution.lean", self.source), ("submission.draft.json", self.server),
                ("LICENSE", (OLD / "LICENSE").read_bytes()), ("ATTRIBUTION.zh.md", attribution),
                ("MATHEMATICS.zh.md", note.encode()), ("mathematical-source-check.json", (OLD / "mathematical-source-check.json").read_bytes()),
                ("source-wire-policy.json", (OLD / "source-wire-policy.json").read_bytes())):
            write_new(NEW / name, raw)
        for name, value in (("proof/Solution.manifest.json", proof), ("website-fields.draft.json", fields),
                ("verification-status.json", status), ("evidence-references.json", references),
                ("provenance.json", provenance), ("official-attempt-basis.json", self.basis), ("expected-wire.json", prediction)):
            write_new(NEW / name, encoded(value))
        write_new(NEW / "README.zh.md", ("本attempt-v8包按macro012和用户已明确的直接尝试授权生成，依据是已披露两次本地失败后的官网尝试，不是local PASS。raw source542421…/1829382B、form server JSON d88b…及expected bundle " + WIRE_SHA + " 不变；Li Xiang/lixiang90、605字符summary、原p/q、model=null、Codex及许可均保留。\n\n"
            "v1实际parent54132/child12924、outer1由旧commit线停止；RSS-only v2实际parent35104/child5564、原93095 outer1及Lean memory_exception保全。ATTRIBUTION首句纠正为准确v8与继承关系，旧DRAFT/pending/错误PID快照不改。所有verification/PASS/双核/full3200/官方接受/上传ready标志仍false或unknown，尚未上传。\n\n"
            "不运行旧ready生成器，不本地重跑，不提高-M6500、不修改InfoTree或证明源；只由root后续操作官网原8GB/3200完整验收。准备材料本身不提交、不调用API、网络、Lean或内核。未来官网actual结果另建addendum，不改本包源。\n").encode())
        self.immutable()
        require((NEW / "proof/Solution.lean").read_bytes() == self.source
                and (NEW / "submission.draft.json").read_bytes() == self.server, "Output raw wire bytes changed")
        rows = [{"path": path.relative_to(NEW).as_posix(), "bytes": path.stat().st_size,
                 "sha256": sha(path.read_bytes())} for path in sorted(NEW.rglob("*")) if path.is_file()]
        write_new(NEW / "files.json", encoded({"schema": "w9a2-official-attempt-v8-files-v1", "scope": BASIS,
            "source_sha256": SOURCE_SHA, "expected_wire_digest": WIRE_SHA,
            "local_resource_PASS": False, "submitted": False, "official_website_acceptance": False,
            "upload_ready": False, "files": rows}))
        print(json.dumps({"attempt_directory": str(NEW), "manifest_sha256": sha((NEW / "files.json").read_bytes()),
            "source_sha256": SOURCE_SHA, "expected_wire_digest": WIRE_SHA,
            "local_resource_PASS": False, "submitted": False, "official_accepted": False}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gate", required=True)
    parser.add_argument("--gate-sha256", required=True)
    args = parser.parse_args()
    attempt = Preparation(args)
    attempt.validate()
    attempt.generate()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
