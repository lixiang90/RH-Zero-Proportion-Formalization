"""Prepare a NEW compiler-resource-reviewed v8 package only from future actual success.

Prepared source only: do not run before root freezes a NEW enabled metadata gate.
No proof process, API, version probe, network, browser or Git action is performed.
"""
from __future__ import annotations
import argparse
import copy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
OLD = ROOT / "submission/w9a2-weighted-potential-20261020-prepared-v8"
WIRE = ROOT / "submission/w9a2-weighted-potential-20261020-expected-wire-v8"
READY = ROOT / "submission/w9a2-weighted-potential-20261020-ready-v8"
DRAFT = ROOT / "research-goal-20261020-w9a2-delivery/draft-v8"
START = ROOT / "research-goal-20261020-w9a2-v8-resource-observation-v2"
WORK = ROOT / "tmp/w9a2-20261020/v8-resource-v2"
RESOURCE_RUNNER = ROOT / "research-goal-20261020-w9a2-v8-resource-preparation-v3/run_resource.py"
RESOURCE_GATE = ROOT / "research-goal-20261020-w9a2-v8-resource-gate-v2/gate.json"
SOURCE_SHA = "5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b"
RESOURCE_RUNNER_SHA = "d47d98607df23d7711176116ce62fa13d85925f5c634af1175cc74ef7b3ad880"
RESOURCE_GATE_SHA = "bcf095c4b96c79e9be3b9552e862fd16f3f3827a475a6ff34a5ed082786d51a4"
SERVER_SHA = "d88b70050b2a1e1a69d2e1044bcc6a3d1a75c56ab8342f8559f77fe9b270362a"
WIRE_SHA = "fb457eecc550ce09bee528294dfff90137631c08e95fa26ffba1e99ec4e11bd4"
LIMIT = 7 * 1024**3


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read_json(path):
    return json.loads(path.read_bytes())


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def write_new(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as stream:
        stream.write(raw)


def real_number(value):
    return type(value) in (int, float)


class Preparation:
    def __init__(self, args):
        self.args = args
        self.inputs = {}

    def path(self, value):
        require(isinstance(value, str) and value, "Missing path")
        path = Path(value)
        if not path.is_absolute():
            path = ROOT / path
        path = path.resolve()
        require(path.is_relative_to(ROOT.resolve()), "Evidence path escaped workspace")
        return path

    def pin(self, path, expected=None, expected_bytes=None):
        digest, size = hashlib.sha256(), 0
        with path.open("rb") as stream:
            while block := stream.read(1024 * 1024):
                digest.update(block)
                size += len(block)
        row = {"path": path.relative_to(ROOT).as_posix(), "bytes": size, "sha256": digest.hexdigest()}
        if expected is not None:
            require(row["sha256"] == expected, "Hash mismatch: " + str(path))
        if expected_bytes is not None:
            require(size == expected_bytes, "Byte-size mismatch: " + str(path))
        self.inputs[str(path)] = row
        return row

    def row(self, row):
        require(isinstance(row, dict) and isinstance(row.get("sha256"), str)
                and len(row["sha256"]) == 64, "Missing exact evidence SHA256")
        path = self.path(row.get("path"))
        self.pin(path, row["sha256"], row.get("bytes"))
        return path

    def manifest(self, path, expected):
        self.pin(path, expected)
        folder = path.parent.resolve()
        members = set()
        for row in read_json(path)["files"]:
            member = (folder / row["path"]).resolve()
            require(member.is_relative_to(folder), "Manifest member escaped its archive")
            require(member not in members, "Duplicate manifest member")
            self.pin(member, row["sha256"], row["bytes"])
            members.add(member)
        return members

    def immutable(self):
        for path, row in list(self.inputs.items()):
            self.pin(Path(path), row["sha256"], row["bytes"])

    def validate(self):
        require(__debug__, "Optimized Python is not supported")
        gate_path = self.path(self.args.gate)
        self.pin(gate_path, self.args.gate_sha256)
        gate = read_json(gate_path)
        require(gate.get("schema") == "w9a2-submission-authoritative-v8-gate-v1", "Wrong metadata-gate schema")
        require(gate.get("allow_material_generation") is True and gate.get("proposal_only") is False,
                "Disabled proposal cannot generate a ready package")
        require(gate.get("sole_owner") == "/root", "Root ownership required")
        self.pin(Path(__file__).resolve(), gate.get("generator_sha256"))
        require(isinstance(gate.get("generator_sha256"), str) and len(gate["generator_sha256"]) == 64,
                "Missing generator source pin")
        require(self.path(gate["output_directory"]) == READY.resolve() and not READY.exists(),
                "Exclusive ready-v8 output already exists or path changed")
        self.manifest(OLD / "files.json", "5bfb2d54a88cf28dd2b0b5b413bf3e5df5f3967d04d85d4037f93eddf051ca1e")
        self.manifest(WIRE / "files.json", "7be638eb265f940efaecd305d4a0a8db9d4fedc4cd4c640d974939979eadad25")
        self.manifest(DRAFT / "files.json", "7f449697314ee04088f1874a6cfdd609c02bb322995feb1197406133ded2a776")
        self.manifest(ROOT / "research-goal-20261020-w9a2-v8-materials-static-independent/files.json",
                      "36338e03f7b4244bfab594498d1e97bba076b484fdb0fcb3f42827860edb4ff2")
        self.manifest(START / "files.json", "99b28dcdb9ee5152c5e86c122f67b0abbefe6904afc0321aac58892d40c19ff5")
        archive_manifest = self.row(gate["resource_success_archive_manifest"])
        members = self.manifest(archive_manifest, gate["resource_success_archive_manifest"]["sha256"])
        outer_path = self.row(gate["root_original_outer_observation"])
        terminal_path = self.row(gate["archived_resource_terminal"])
        require(outer_path in members and terminal_path in members, "Actual success evidence must belong to the pinned archive")
        outer, terminal = read_json(outer_path), read_json(terminal_path)
        require(outer.get("schema") == "w9a2-v8-resource-root-outer-observation-v1"
                and outer.get("role") == "v8-resource-v2", "Wrong root outer observation protocol")
        require(type(outer.get("original_tool_session")) is int and outer["original_tool_session"] == 93095,
                "The original outer handle must be 93095")
        require(outer.get("parent_pid") == 35104, "Wrong original parent role")
        if "child_pid" in outer:
            require(outer["child_pid"] == 5564, "Wrong compiler child role")
        require(type(outer.get("actual_original_parent_exit_code")) is int
                and outer["actual_original_parent_exit_code"] == 0, "Original outer did not actually exit0")
        raw = outer.get("actual_original_handle_result")
        require(isinstance(raw, dict) and type(raw.get("exit_code")) is int and raw["exit_code"] == 0,
                "Actual original write_stdin result with exit0 is required")
        require(outer.get("runner_sha256") == RESOURCE_RUNNER_SHA and outer.get("gate_sha256") == RESOURCE_GATE_SHA,
                "Outer runner/gate binding mismatch")
        terminal_pin = self.pin(terminal_path)
        require(outer.get("printed_terminal_sha256_from_original_tool_result") == terminal_pin["sha256"],
                "Root must bind the actually printed terminal SHA")
        outer_terminal_path = self.row(outer["terminal_receipt"])
        require(outer_terminal_path in {terminal_path, (WORK / "terminal.json").resolve()},
                "Root terminal pointer is neither the original work receipt nor its archived copy")
        require(self.pin(outer_terminal_path)["sha256"] == terminal_pin["sha256"],
                "Original and archived terminal bytes differ")
        printed = []
        for line in raw.get("output", "").splitlines():
            try:
                value = json.loads(line)
            except (ValueError, TypeError):
                continue
            if isinstance(value, dict) and value.get("terminal_sha256") == terminal_pin["sha256"]:
                printed.append(value)
        require(len(printed) == 1, "Original output must contain exactly one actual printed terminal-SHA record")
        require(self.path(printed[0].get("terminal")) == (WORK / "terminal.json").resolve(),
                "Original printed terminal path belongs to another attempt")
        require(printed[0].get("compiler_resource_gate_passed") is True
                and type(printed[0].get("actual_child_exit_code")) is int and printed[0]["actual_child_exit_code"] == 0
                and printed[0].get("parent_exit_code_to_return") == 0, "Printed terminal record is not resource success")
        external_elapsed = outer.get("actual_same_clock_parent_completion_elapsed_seconds")
        require(real_number(external_elapsed) and 0 < external_elapsed <= 3200,
                "Actual same-clock original parent completion must be within3200 seconds")
        require(terminal.get("schema") == "w9a2-v8-compiler-resource-terminal-v2", "Wrong terminal schema")
        require(terminal.get("parent_pid") == 35104 and terminal.get("child_pid") == 5564
                and terminal.get("monotonic_t0") == 29449.203, "Wrong actual attempt identity or clock")
        require(type(terminal.get("actual_child_exit_code")) is int and terminal["actual_child_exit_code"] == 0,
                "Compiler child did not actually return0")
        for key in ("compiler_resource_gate_passed", "candidate_compile_and_C_generation_completed", "final_memory_query_succeeded"):
            require(terminal.get(key) is True, "Missing actual resource PASS field: " + key)
        require(terminal.get("failure") is None and terminal.get("resource_limit_exceeded") is False
                and terminal.get("budget_expired_and_owned_child_terminated") is False, "Resource attempt failed or was stopped")
        require(terminal.get("metric") == "PeakWorkingSetSize" and terminal.get("commit_diagnostic_only") is True,
                "Only the reviewed RSS resource metric is acceptable")
        require(terminal.get("observed_peak_stop_bytes") == LIMIT and terminal.get("compiler_memory_flag_MiB") == 6500
                and terminal.get("total_budget_seconds") == 3200, "Resource limits changed")
        require(type(terminal.get("max_observed_PeakWorkingSetSize")) is int
                and 0 < terminal["max_observed_PeakWorkingSetSize"] < LIMIT, "RSS peak was not valid below the gate")
        require(type(terminal.get("max_observed_PeakPagefileUsage")) is int
                and terminal["max_observed_PeakPagefileUsage"] >= 0, "Missing diagnostic commit peak")
        elapsed = terminal.get("elapsed_seconds")
        require(real_number(elapsed) and 0 < elapsed <= 3200 and elapsed <= external_elapsed,
                "Terminal clock is not a completed within-budget original parent attempt")
        require(terminal.get("automatic_retries") == 0 and terminal.get("automatic_repairs") == 0
                and terminal.get("cached_user_Candidate_imported") is False, "Wrong resource execution scope")
        self.pin(RESOURCE_RUNNER, RESOURCE_RUNNER_SHA)
        self.pin(RESOURCE_GATE, RESOURCE_GATE_SHA)
        resource_gate = read_json(RESOURCE_GATE)
        require(resource_gate["schema"] == "w9a2-v8-resource-gate-v2"
                and resource_gate["metric"] == "PeakWorkingSetSize" and resource_gate["commit_diagnostic_only"] is True,
                "Pinned resource gate has wrong metric")
        require(self.row(terminal["gate"]) == RESOURCE_GATE.resolve(), "Terminal gate pin differs from actual gate")
        source = DRAFT / "Solution.lean"
        self.pin(source, SOURCE_SHA, 1829382)
        require(self.row(terminal["source"]) == source.resolve(), "Terminal source is not exact draft-v8")
        fresh_source = self.row(terminal["fresh_source_copy"])
        require(fresh_source == (WORK / "source/Solution/Candidate.lean").resolve(), "Wrong fresh source path")
        self.pin(fresh_source, SOURCE_SHA, 1829382)
        require(terminal["compiler_argv"] == read_json(START / "started.json")["compiler_argv"]
                == read_json(START / "child.json")["argv"], "Actual compiler argv differs from frozen startup")
        argv = terminal["compiler_argv"]
        for flag in ("-j1", "-M6500", "--tstack=262144", "--json"):
            require(flag in argv, "Missing fixed compiler flag")
        require("--run" not in argv and "--setup" not in argv, "Unexpected replay or official setup command")
        outputs = terminal.get("output_artifacts")
        expected_outputs = {(WORK / ("output/Solution/Candidate" + ext)).resolve() for ext in (".olean", ".ilean", ".c")}
        require(isinstance(outputs, list) and len(outputs) == 3, "Exactly three completed compiler outputs are required")
        observed_outputs = set()
        for row in outputs:
            path = self.row(row)
            require(path in expected_outputs and path not in observed_outputs and row["bytes"] > 0,
                    "Missing/duplicate/nonfresh compiler artifact")
            observed_outputs.add(path)
        require(observed_outputs == expected_outputs, "Incomplete compiler/C-generation artifacts")
        for flag, extension in (("-o", ".olean"), ("-i", ".ilean"), ("-c", ".c")):
            require(argv.count(flag) == 1 and self.path(argv[argv.index(flag) + 1])
                    == (WORK / ("output/Solution/Candidate" + extension)).resolve(), "Compiler output argv mismatch")
        old_failure = ROOT / "research-goal-20261020-w9a2-v8-resource-failure-v1"
        self.manifest(old_failure / "files.json", "8317a845b841313d4042ae0664a9d38039e96fe05adedee868355636a13a0cf1")
        old_outer = read_json(old_failure / "root-outer-observation.json")
        require(old_outer["original_outer_session_id"] == 72573 and old_outer["actual_original_outer_exit_code"] == 1
                and old_outer["parent_pid"] == 54132 and old_outer["child_pid"] == 12924, "Historical v1 failure roles changed")
        source_raw = source.read_bytes()
        require((OLD / "proof/Solution.lean").read_bytes() == source_raw, "DRAFT source bytes changed")
        server = (WIRE / "expected-server-submission.json").read_bytes()
        require((OLD / "submission.draft.json").read_bytes() == server and sha(server) == SERVER_SHA,
                "Exact server metadata changed")
        require(sha(b"submission.json\0" + server + b"proof/Solution.lean\0" + source_raw) == WIRE_SHA,
                "Frozen wire digest changed")
        self.result = {"archive_manifest": self.pin(archive_manifest), "root_outer_observation": self.pin(outer_path),
            "resource_terminal": terminal_pin, "source": self.pin(source), "compiler_outputs": outputs,
            "original_outer_session": 93095, "parent_pid": 35104, "child_pid": 5564,
            "actual_outer_exit_code": 0, "actual_child_exit_code": 0,
            "terminal_elapsed_seconds": elapsed, "actual_same_clock_parent_completion_elapsed_seconds": external_elapsed,
            "peak_working_set_bytes": terminal["max_observed_PeakWorkingSetSize"],
            "diagnostic_peak_commit_bytes": terminal["max_observed_PeakPagefileUsage"],
            "scope": "Ordinary Lean compiler plus C generation and RSS observation only; no exporter or separate kernel replay"}
        self.source_raw, self.server_raw = source_raw, server
        self.immutable()  # Includes this generator, root actual success evidence and all three outputs.

    def generate(self):
        require(not READY.exists(), "Ready package already exists")
        proof = copy.deepcopy(read_json(OLD / "proof/Solution.manifest.json"))
        status = {"schema": "w9a2-ready-v8-compiler-only-status-v1", "prepared_at_UTC": datetime.now(timezone.utc).isoformat(),
            "source": proof, "compiler_C_generation_resource_gate_passed": True,
            "single_file_ordinary_compile_passed": True,
            "ordinary_modular_complete_actual_Lean_passed": False,
            "resource_result": "actual_RSS_gate_compiler_and_C_generation_PASS_only", "resource_evidence": self.result,
            "Lean_ordinary_compile_includes_inherent_kernel_type_checking": True,
            "Comparator_statement_dependency_primitive_passed": False, "Comparator_transitive_axioms_passed": False,
            "default_Lean_kernel_replay_passed": False, "independent_serial_nanoda_passed": False,
            "mathematical_dual_kernel_complete": False, "complete_single_3200s_production_passed": False,
            "official_website_result_observed": False, "official_website_acceptance_confirmed": False,
            "official_verdict": None, "submitted": False, "upload_ready": False,
            "ready_for_root_submission_review": True,
            "readiness_scope": "Ready-named review package only after compiler-resource PASS; posting remains a separate root action and official two-kernel/full-pipeline checks remain pending",
            "historical_pending_reports_are_not_current_state": True,
            "historical_v1": {"original_outer_session": 72573, "actual_parent_pid": 54132, "actual_child_pid": 12924,
                "actual_outer_exit_code": 1, "actual_child_exit_code": 1, "result": "own_runner_commit_threshold_stop; not OOM/math rejection"},
            "future_official_results_require_separate_addendum": True,
            "compiler_export_kernel_network_UI_process_calls_by_this_generator": 0}
        fields = copy.deepcopy(read_json(OLD / "website-fields.draft.json"))
        fields.update(upload_ready=False, submitted=False, official_website_acceptance=False, ready_for_root_submission_review=True)
        provenance = {"schema": "w9a2-authoritative-ready-v8-provenance-v1", "exact_source": self.result["source"],
            "source_copied_without_normalization": True, "old_DRAFT_preserved": self.pin(OLD / "files.json"),
            "DRAFT_findings_independent_review": self.pin(ROOT / "research-goal-20261020-w9a2-v8-materials-static-independent/files.json"),
            "ATTRIBUTION_first_sentence_corrected_only_in_new_package": True,
            "embedded_source_notices_and_LICENSE_unchanged": True,
            "actual_compiler_resource_evidence": self.result, "official_or_dual_kernel_PASS_claimed": False,
            "historical_v1_parent_child_roles_corrected_by_actual_records": {"parent": 54132, "child": 12924},
            "actual_v2_parent_child_roles": {"parent": 35104, "child": 5564},
            "current_resource_state_is_not_inherited_DRAFT_pending": True}
        references = {"schema": "w9a2-ready-v8-actual-evidence-references-v1", "resource_evidence": self.result,
            "frozen_draft_source_manifest": self.pin(DRAFT / "files.json"),
            "historical_DRAFT_package": self.pin(OLD / "files.json"),
            "historical_DRAFT_pending_is_not_current": True,
            "historical_v1_failed_resource_archive": self.pin(ROOT / "research-goal-20261020-w9a2-v8-resource-failure-v1/files.json"),
            "current_v2_start_archive": self.pin(START / "files.json"),
            "exact_unchanged_wire_package": self.pin(WIRE / "files.json"),
            "expected_wire_digest": WIRE_SHA, "actual_official_receipt": None}
        attribution = (OLD / "ATTRIBUTION.zh.md").read_bytes()
        old_sentence = "proof/Solution.lean是draft-v5原始字节的完整副本。".encode()
        require(attribution.count(old_sentence) == 1 and attribution.startswith(old_sentence), "Unexpected attribution baseline")
        new_sentence = ("proof/Solution.lean是冻结draft-v8原始字节的完整副本（1829382字节，SHA256 " + SOURCE_SHA + "）。"
            "该源沿draft-v5→v6（3处wfun全名）、v6→v7（8处显式noncomputable并删15行#print诊断）、v7→v8（PTT_0..7、PTT、PT共10处显式noncomputable）继承，逐版精确差分及旧证据保全。").encode()
        attribution = new_sentence + attribution[len(old_sentence):]
        note = (OLD / "MATHEMATICS.zh.md").read_text(encoding="utf-8")
        require("以上数学说明沿用历史冻结材料。" in note, "Unexpected inherited mathematics note")
        note = note.split("以上数学说明沿用历史冻结材料。", 1)[0] + "以上数学说明沿用冻结v8源码与历史材料。新RSS门原session93095、parent35104/child5564已由实际收据证明普通Lean编译和C生成完成，并符合本地RSS测量合同。这个compiler-only PASS不包含独立Comparator/default-kernel/Nano重放、官网双核或完整3200秒pipeline验收，尚未上传。旧v1资源运行72573的parent54132/child12924因旧commit阈值退出1，旧pending仅是当时快照，均不改写或提升为PASS。\n"
        formulas = copy.deepcopy(read_json(OLD / "mathematical-source-check.json"))
        formulas["scope"] = "Inherited exact mathematical description; latest actual evidence is ordinary Lean compilation plus C generation only, no separate independent replay or official acceptance"
        formulas.pop("v8_mathematical_verification_performed", None)
        formulas["independent_mathematical_replay_performed"] = False
        formulas["actual_compiler_resource_evidence_only"] = True
        READY.mkdir(parents=True, exist_ok=False)
        for name, raw in (("proof/Solution.lean", self.source_raw), ("submission.draft.json", self.server_raw),
                ("LICENSE", (OLD / "LICENSE").read_bytes()), ("ATTRIBUTION.zh.md", attribution),
                ("MATHEMATICS.zh.md", note.encode()), ("source-wire-policy.json", (OLD / "source-wire-policy.json").read_bytes())):
            write_new(READY / name, raw)
        for name, value in (("proof/Solution.manifest.json", proof), ("website-fields.draft.json", fields),
                ("verification-status.json", status), ("provenance.json", provenance),
                ("evidence-references.json", references), ("mathematical-source-check.json", formulas),
                ("compiler-resource-addendum.json", self.result)):
            write_new(READY / name, encoded(value))
        write_new(READY / "README.zh.md", ("本新ready-v8包只在原93095实际outer0、parent35104/child5564、资源terminal PASS及三个fresh输出SHA全部核同后生成。原始proof、server metadata与预期bundle " + WIRE_SHA + " 不变。ATTRIBUTION首句改为准确draft-v8及继承关系；旧DRAFT快照不改。\n\n"
            "实际结果仅是普通Lean compiler/C-generation/RSS门通过；独立双核、官网完整3200秒pipeline与官方接受未通过，尚未上传。ready仅表示可供root审阅，本包upload_ready=false，不自动提交、重放或编译。旧v1运行parent54132/child12924的commit-stop失败和旧pending保全；本次current状态由actual v2成功收据另立。后续官网结果必须另存addendum，不改本包源。\n").encode())
        self.immutable()
        require((READY / "proof/Solution.lean").read_bytes() == self.source_raw
                and (READY / "submission.draft.json").read_bytes() == self.server_raw, "Output wire bytes changed")
        rows = [{"path": path.relative_to(READY).as_posix(), "bytes": path.stat().st_size,
                 "sha256": sha(path.read_bytes())} for path in sorted(READY.rglob("*")) if path.is_file()]
        write_new(READY / "files.json", encoded({"schema": "w9a2-authoritative-ready-v8-files-v1",
            "scope": "Actual resource compiler-only PASS; no independent two-kernel/full-pipeline/official PASS or upload",
            "source_sha256": SOURCE_SHA, "expected_wire_digest": WIRE_SHA,
            "submitted": False, "official_website_acceptance": False, "upload_ready": False, "files": rows}))
        print(json.dumps({"ready_directory": str(READY), "manifest_sha256": sha((READY / "files.json").read_bytes()),
            "source_sha256": SOURCE_SHA, "wire_digest": WIRE_SHA, "resource_compiler_only_PASS": True,
            "submitted": False, "official_accepted": False}), flush=True)


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
