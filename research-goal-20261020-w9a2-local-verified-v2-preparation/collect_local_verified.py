"""Future receipt-only collector. PREPARED, NOT RUN.

Refuses until root pins the original fullchain-v2 handle's actual exit0.
Never imports a runner, invokes subprocess/network, or evaluates Lean.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
WORK = ROOT / "tmp/w9a2-20261020/fullchain-v2"
PREPARED = ROOT / "submission/w9a2-weighted-potential-20261020-prepared-v6"
WIRE = ROOT / "submission/w9a2-weighted-potential-20261020-expected-wire-v6"
DESTINATION = ROOT / "submission/w9a2-weighted-potential-20261020-local-verified-v2"
SOURCE_SHA = "a517df6aebde6d136f8b83e06c8be10b3413b8430390f52bd47f04e06f0dce26"
RUNNER_SHA = "92cc8dcf3e3c46e76490ba7bfe8d93bc10e331131eaab3b4c3ae500f80ac66a8"
GATE_SHA = "3ebcc3b75ee2a75775281a2a0e9321f7610baddcab5965fcf002fd51e2d763fd"
PREPARED_SHA = "55c28b9f90515324f40144822d9e84b301fe9001ec1a03e8df2bf1350159522f"
EXPECTED_MANIFEST_SHA = "e9aace57386e2bbf5ef9db3ad4bb8585db7173b315141b13bee6b1646bd00ec2"
WIRE_MANIFEST_SHA = "f81666062165a2a1e60bd59b88cedcc237e72bebe9faca0f183b021fec636851"
EXPECTED_PROOF_DIGEST = "e76462f687d4e95d7f9f2ebb558bd5d2d5452814f01e54fd657856dbb12157d1"
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}
TARGETS = {"candidate_strict_improvement", "candidate_critical_line_bound", "candidate_critical_line_bound_cumulative"}
LABELS = ["compiler-version", "ordinary-ChallengeDeps", "ordinary-ChallengeDeps.CandidateSpec",
    "ordinary-Challenge.Candidate", "ordinary-Solution.Candidate", "challenge-native-export",
    "solution-native-export", "comparator-default-Lean-kernel", "serial-nanoda"]


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def zero(value):
    return type(value) is int and value == 0


def number(value):
    return type(value) in (int, float) and math.isfinite(value)


def sha(path):
    result = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
            result.update(block)
    return result.hexdigest()


def path(value):
    item = Path(value)
    resolved = (item if item.is_absolute() else ROOT / item).resolve()
    require(resolved.is_relative_to(ROOT.resolve()), "Input leaves workspace")
    return resolved


def load(item):
    return json.loads(Path(item).read_bytes())


class Pins:
    def __init__(self):
        self.rows = {}

    def current(self, value, expected=None, size=None):
        item = path(value)
        require(item.is_file(), "Missing actual completed evidence: " + str(item))
        actual = sha(item)
        require(expected is None or actual == expected, "SHA mismatch: " + str(item))
        require(size is None or item.stat().st_size == size, "Size mismatch: " + str(item))
        row = {"path": item.relative_to(ROOT.resolve()).as_posix(), "bytes": item.stat().st_size, "sha256": actual}
        require(str(item) not in self.rows or self.rows[str(item)] == row, "Conflicting evidence pin")
        self.rows[str(item)] = row
        return item

    def row(self, row):
        return self.current(row["path"], row["sha256"], row.get("bytes"))

    def manifest(self, directory, expected=None):
        source = self.current(directory / "files.json", expected)
        data = load(source)
        require(data["files"], "Empty manifest")
        for row in data["files"]:
            item = path(directory / row["path"])
            require(item.is_relative_to(directory.resolve()), "Manifest escape")
            self.current(item, row["sha256"], row["bytes"])
        return data

    def immutable(self):
        for filename, row in self.rows.items():
            require(path(filename) == Path(filename) and Path(filename).stat().st_size == row["bytes"] and
                sha(filename) == row["sha256"], "Evidence changed during collection")


def write(relative, raw):
    target = DESTINATION / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    with target.open("xb") as output:
        output.write(raw)
        output.flush()
        os.fsync(output.fileno())


def dump(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def copy_pinned(relative, source, pins):
    raw = source.read_bytes()
    row = pins.rows[str(source.resolve())]
    require(len(raw) == row["bytes"] and hashlib.sha256(raw).hexdigest() == row["sha256"],
        "Pinned evidence changed before copy")
    write(relative, raw)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--outer-observation", required=True)
    parser.add_argument("--outer-observation-sha256", required=True)
    parser.add_argument("--preparation-manifest-sha256", required=True)
    args = parser.parse_args()
    require(__debug__, "Use Python without optimization")
    require(not DESTINATION.exists(), "Never overwrite a previous local evidence package")
    pins = Pins()
    preparation = pins.manifest(HERE, args.preparation_manifest_sha256)
    require(str(path(__file__)) in pins.rows, "Collector source is not pinned")
    prepared = pins.manifest(PREPARED, PREPARED_SHA)
    require(len(prepared["files"]) == 13, "Prepared 13-file scope changed")
    source = pins.current(PREPARED / "proof/Solution.lean", SOURCE_SHA, 1830052)
    actual_source = pins.current(WORK / "source/Solution/Candidate.lean", SOURCE_SHA, 1830052)
    require(source.read_bytes() == actual_source.read_bytes(), "Production source is not exact frozena517")
    require(not (WORK / "failure.json").exists(), "Failure receipt is present")
    start_path = pins.current(WORK / "started.json"); started = load(start_path)
    require(started["pid"] == 49320 and started["monotonic_t0"] == 11264.218 and
        started["gate_sha256"] == GATE_SHA and started["budget_seconds"] == 3200 and
        started["platform"] == "windows-native-wsl-nanoda", "Wrong original production start")
    verify_path = pins.current(WORK / "verification.json"); verify = load(verify_path)
    deadline_path = pins.current(WORK / "deadline-receipt.json"); deadline = load(deadline_path)
    terminal_path = pins.current(WORK / "terminal.json"); terminal = load(terminal_path)
    require(deadline["verification_sha256"] == terminal["verification_sha256"] == sha(verify_path) and
        terminal["deadline_receipt_sha256"] == sha(deadline_path), "The three receipts are not hash linked")
    require(verify["schema"] == "w9a2-fullchain-verification-v1" and verify["failed"] is False and
        verify["local_fullchain_verified"] is True and verify["stage"] == "all-proof-stages-passed" and
        verify["monotonic_t0"] == started["monotonic_t0"] and verify["budget_seconds"] == 3200,
        "Full production receipt is incomplete")
    require(verify["sole_owner"] == "/root" and verify["platform"] == started["platform"] and
        verify["gate_sha256"] == started["gate_sha256"], "Production gate identity changed")
    gate_path = pins.current(verify["gate_path"], GATE_SHA); gate = load(gate_path)
    runner_path = pins.current(ROOT / "research-goal-20261020-w9a2-verification-preparation-v1/run_verification.py", RUNNER_SHA)
    require(gate["runner_sha256"] == RUNNER_SHA and gate["allow_verification_execution"] is True and
        gate["proposal_only"] is False and gate["cached_user_oleans"] is False and
        gate["total_budget_seconds"] == 3200 and gate["automatic_retries"] == gate["automatic_repairs"] == 0 and
        path(gate["work_directory"]) == WORK.resolve(), "Production contract/gate changed")
    require(verify["automatic_repairs"] == verify["automatic_retries"] == 0 and
        verify["cached_user_oleans_used"] is False and verify["complete_source_and_bound_artifacts_unchanged"] is True and
        verify["source_freshly_regenerated_inside_budget"] is True and verify["source_bytes"] == 1830052 and
        verify["source_sha256"] == SOURCE_SHA and verify["trusted_spec_generated_from_exact_checked_rationals"] is True and
        verify["fresh_record_checked_at_start"] is True, "Fresh exact source/spec or no-reuse checks are missing")
    for name in ["ordinary_single_file_passed", "Comparator_statement_dependency_primitive_passed",
                 "Comparator_transitive_axioms_passed", "default_Lean_kernel_replay_passed", "serial_nanoda_passed"]:
        require(verify[name] is True, "A required proof gate did not pass: " + name)
    require(zero(verify["nanoda_num_threads"]) and type(verify["nanoda_checked_declarations"]) is int and
        verify["nanoda_checked_declarations"] > 0 and set(verify["nanoda_printed_axioms"]) <= ALLOWED,
        "Independent serial Nano receipt is incomplete")
    require(TARGETS <= set(verify["ordinary_printed_axioms"]) and
        all(set(value) <= ALLOWED for value in verify["ordinary_printed_axioms"].values()), "Ordinary public/transitive axiom audit changed")
    require(terminal["full_chain_and_hashes_completed"] is True and zero(terminal["completion_return_code"]) and
        terminal["actual_process_exit0_must_be_observed_by_outer_handle"] is True and
        terminal["failure_receipt_must_be_absent"] is True and deadline["within_total_limit"] is True and
        deadline["total_limit_seconds"] == 3200, "Final receipt or budget completion missing")
    require(verify["official_website_acceptance"] is False and verify["submitted"] is False and
        deadline["official_website_acceptance"] is False and terminal["official_website_acceptance"] is False,
        "Local receipt claims an official result")
    observation_path = pins.current(args.outer_observation, args.outer_observation_sha256); outer = load(observation_path)
    require(outer["schema"] == "w9a2-root-terminal-observation-v1" and outer["sole_owner"] == "/root" and
        outer["role"] == "fullchain-v2" and outer["exec_session_id"] == 68962 and outer["parent_pid"] == 49320 and
        zero(outer["actual_exit_code"]) and outer["observed_scope"] == "completed-outer-parent-handle" and
        outer["observation_source"] in ["functions.exec_command", "functions.write_stdin"], "Wrong actual root outer-handle observation")
    require(pins.row(outer["runner"]) == runner_path and outer["runner"]["sha256"] == RUNNER_SHA and
        pins.row(outer["completion_receipt"]) == terminal_path, "Outer observation names another runner/terminal")
    if "gate" in outer:
        require(pins.row(outer["gate"]) == gate_path, "Outer gate pin differs")
    raw_path = pins.row(outer["raw_tool_terminal"]); raw = load(raw_path)
    require(zero(raw.get("exit_code")) and isinstance(raw.get("output"), str) and
        raw.get("session_id") in [None, 68962], "Actual outer tool exit/output is missing")
    completions = []
    for line in raw["output"].splitlines():
        try:
            value = json.loads(line)
        except (ValueError, TypeError):
            continue
        if isinstance(value, dict) and "total_elapsed_through_all_fsynced_receipts_seconds" in value:
            completions.append(value)
    require(len(completions) == 1, "Actual original-handle output lacks one final receipt message")
    final = completions[0]
    require(final["local_fullchain_verified"] is True and final["terminal_sha256"] == sha(terminal_path) and
        path(final["work_directory"]) == WORK.resolve() and zero(final["root_must_observe_actual_process_exit_code"]) and
        final["official_website_acceptance"] is False, "Outer final terminal hash/scope differs")
    elapsed = [verify["elapsed_before_final_receipts_seconds"], deadline["elapsed_after_fsynced_verification_seconds"],
        terminal["elapsed_before_terminal_fsync_seconds"], final["total_elapsed_through_all_fsynced_receipts_seconds"]]
    require(all(number(value) for value in elapsed) and 0 < elapsed[0] <= elapsed[1] <= elapsed[2] <= elapsed[3] < 3200,
        "Same-clock complete receipt chain does not finish below3200s")
    observed_time = datetime.fromisoformat(outer["observed_at_utc"].replace("Z", "+00:00"))
    began = datetime.fromisoformat(verify["started_at_utc"].replace("Z", "+00:00"))
    require(observed_time.tzinfo is not None and began.tzinfo is not None and began <= observed_time <= datetime.now(timezone.utc),
        "Outer observation time is future-dated or precedes the actual verification")
    stages = verify["stages"]
    require([stage["label"] for stage in stages] == LABELS, "Missing or extra production proof stages")
    require(verify["compiled_modules"] == stages[1:5] and
        [stage["module"] for stage in verify["compiled_modules"]] ==
            ["ChallengeDeps", "ChallengeDeps.CandidateSpec", "Challenge.Candidate", "Solution.Candidate"] and
        stages[4]["source_sha256"] == SOURCE_SHA, "Ordinary exact four-module source records differ")
    owned_evidence = [start_path, verify_path, deadline_path, terminal_path, observation_path, raw_path,
        gate_path, runner_path, pins.current(WORK / "generation.json"), pins.current(WORK / "nanoda-config.json")]
    generation = load(WORK / "generation.json")
    require(generation["source_bytes"] == 1830052 and generation["source_sha256"] == SOURCE_SHA and
        generation["fresh_source_generation"] is True and generation["cached_user_oleans"] is False,
        "Actual fresh generation receipt changed")
    last_end = started["monotonic_t0"]
    for stage in stages:
        label = stage["label"]
        require(zero(stage["exit_code"]) and type(stage["pid"]) is int and stage["pid"] > 0 and
            number(stage["started_monotonic"]) and number(stage["elapsed_seconds"]) and stage["elapsed_seconds"] >= 0 and
            stage["started_monotonic"] >= last_end and
            0 < stage["remaining_total_budget_seconds"] <= 3200 and path(stage["cwd"]) == WORK.resolve(), "Stage actual exit/clock missing")
        last_end = stage["started_monotonic"] + stage["elapsed_seconds"]
        require(last_end <= started["monotonic_t0"] + elapsed[-1], "Stage exceeds final same-clock completion")
        log = pins.current(stage["log"], stage["log_sha256"])
        require(log == (WORK / "logs" / (label + ".log")).resolve(), "Stage log path changed")
        owned_evidence.append(log)
        for suffix in ["started", "child", "terminal"]:
            item = pins.current(WORK / "logs" / (label + "." + suffix + ".json"))
            data = load(item)
            if suffix == "child":
                require(data == {"pid": stage["pid"], "argv": stage["argv"]}, "Stage child PID/argv differs")
            else:
                require(all(stage.get(key) == value for key, value in data.items()), "Stage receipt differs from full receipt")
            owned_evidence.append(item)
        if "output" in stage:
            pins.current(stage["output"], stage["output_sha256"], stage["output_bytes"])
    require("--wait" in stages[-1]["argv"] and "/usr/bin/setsid" in stages[-1]["argv"] and stages[-1]["wsl_nanoda"] is True,
        "Nano outer command does not explicitly wait for its actual session child")
    audit_text = Path(stages[-2]["log"]).read_text("utf-8")
    for message in ["Pinned Comparator statement, dependency and primitive comparison passed",
        "Pinned Comparator transitive axiom check passed", "Lean default kernel replay passed"]:
        require(message in audit_text, "Locked CoreAudit output missing")
    nano_text = Path(stages[-1]["log"]).read_text("utf-8")
    checked = re.search(r"Checked (\d+) declarations with no errors", nano_text)
    require(checked is not None and int(checked[1]) == verify["nanoda_checked_declarations"], "Nano actual log count differs")
    require([name.split('.{')[0] for name in re.findall(r'^axiom ([^\s]+)', nano_text, re.M)] == verify["nanoda_printed_axioms"],
        "Nano actual log axiom list differs")
    require(load(WORK / "nanoda-config.json") == {"use_stdin": True, "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
        "unpermitted_axiom_hard_error": True, "nat_extension": True, "string_extension": True, "num_threads": 0,
        "unsafe_permit_all_axioms": False, "print_success_message": True, "print_axioms": True, "pp_to_stdout": True}, "Serial Nano config changed")
    # Rehash local production files, exports and logs. SDK/cache files are not
    # recopied or reaudited: the actual frozen runner already checked every bound
    # input through its final immutable() before producing these three receipts.
    owned_pins = []
    for name, digest in verify["bound_sha256"].items():
        candidate = Path(name)
        if candidate.is_absolute() and candidate.is_relative_to(WORK):
            require(candidate.resolve().is_relative_to(WORK.resolve()), "Owned production artifact escaped")
            pins.current(candidate, digest)
            owned_pins.append(pins.rows[str(candidate)])
    require(owned_pins, "No bound fresh production artifacts")
    wire = pins.manifest(WIRE, WIRE_MANIFEST_SHA)
    require({row["path"] for row in wire["files"]} == {"expected-server-submission.json", "prediction.json"}, "Expected wire package changed")
    manifest_path = pins.current(WIRE / "expected-server-submission.json", EXPECTED_MANIFEST_SHA)
    manifest_bytes = manifest_path.read_bytes(); manifest = load(manifest_path)
    require(manifest["model"] is None and manifest["harness"] == "Codex" and
        manifest["author"] == {"github": "lixiang90", "displayName": "Li Xiang"} and
        verify["score"] == gate["score"] == manifest["score"], "Expected optional model/identity/score changed")
    predicted = hashlib.sha256(b"submission.json\0" + manifest_bytes + b"proof/Solution.lean\0" + source.read_bytes()).hexdigest()
    require(predicted == EXPECTED_PROOF_DIGEST and load(WIRE / "prediction.json")["expected_job_proofDigest"] == predicted,
        "Expected manifest/raw source wire digest differs")
    pins.immutable()
    require(not (WORK / "failure.json").exists(), "Failure receipt appeared before package creation")
    DESTINATION.mkdir(parents=True, exist_ok=False)
    for row in prepared["files"]:
        copy_pinned(row["path"], PREPARED / row["path"], pins)
    copy_pinned("evidence/prepared-package-files.json", PREPARED / "files.json", pins)
    for row in wire["files"]:
        copy_pinned("expected-wire/" + row["path"], WIRE / row["path"], pins)
    copy_pinned("expected-wire/files.json", WIRE / "files.json", pins)
    for index, item in enumerate(dict.fromkeys(owned_evidence)):
        relative = ("production/" + item.relative_to(WORK).as_posix()) if item.is_relative_to(WORK) else ("external/" + str(index) + "-" + item.name)
        copy_pinned("evidence/" + relative, item, pins)
    addendum = {"schema": "w9a2-actual-local-verification-addendum-v1", "created_at_utc": datetime.now(timezone.utc).isoformat(),
        "source_sha256": SOURCE_SHA, "source_bytes": 1830052, "original_session": 68962, "original_parent_pid": 49320,
        "runner_sha256": RUNNER_SHA, "gate_sha256": GATE_SHA, "original_monotonic_t0": started["monotonic_t0"],
        "actual_outer_exit_code": 0, "full_single_3200s_production_passed": True,
        "total_elapsed_through_all_fsynced_receipts_seconds": elapsed[-1], "ordinary_single_file_passed": True,
        "Comparator_statement_dependency_primitive_passed": True, "Comparator_transitive_axioms_passed": True,
        "default_Lean_kernel_replay_passed": True, "independent_serial_nanoda_passed": True,
        "nanoda_checked_declarations": verify["nanoda_checked_declarations"], "production_candidate_oleans_reused": False,
        "prepared_13_files_copied_verbatim": True, "prepared_verification_status_is_historical_snapshot": True,
        "this_addendum_is_the_later_local_status": True, "original_prepared_manifest": pins.rows[str((PREPARED / "files.json").resolve())],
        "actual_input_receipt_pins": list(pins.rows.values()), "actual_owned_artifact_pins": owned_pins,
        "large_exports_oleans_SDK_cache_copied": False, "runtime_reaudit_scope": "Production receipt binds original complete runtime audit; collector rehashes owned production files only",
        "model_UI_field": "", "model_expected_server_value": None, "expected_server_manifest_sha256": EXPECTED_MANIFEST_SHA,
        "expected_job_proofDigest": predicted, "official_observed_proofDigest": None,
        "submitted": False, "official_website_acceptance": False, "official_job_id": None,
        "proof_compiler_export_kernel_network_runs_by_collector": 0}
    write("local-verification-addendum.json", dump(addendum))
    write("LOCAL-VERIFICATION.zh.md", ("本包仅在原始生产父句柄实际退出0后生成。根会话68962/PID49320及三份fsync收据、同一monotonic时钟3200秒内完成、所有普通Lean/Comparator/defaultLean/serialNano通过都须由collector逐项核验。\n\n"
        "原prepared的13文件逐字复制，包含当时仍待production的历史verification-status；最新本地状态以local-verification-addendum.json为准。源码a517/1830052字节、署名和许可证未改。expected-wire为预测服务端manifest（model=null），UI模型仍空。\n\n"
        "此包没有官网上传或接受结果：submitted与official_website_acceptance仍false。后续官网结果须另建有hash连接的addendum，不修改本包和源码。大型export/olean/SDK/cache不重复存档，保留实际生产位置及收据绑定。\n").encode())
    local_files = [{"path": item.relative_to(DESTINATION).as_posix(), "bytes": item.stat().st_size, "sha256": sha(item)}
        for item in sorted(DESTINATION.rglob("*")) if item.is_file()]
    write("files.json", dump({"schema": "w9a2-local-verified-evidence-files-v1", "source_sha256": SOURCE_SHA,
        "local_fullchain_verified": True, "submitted": False, "official_website_acceptance": False, "files": local_files}))
    print(json.dumps({"local_package": str(DESTINATION), "manifest_sha256": sha(DESTINATION / "files.json"),
        "source_sha256": SOURCE_SHA, "actual_outer_exit_code": 0, "submitted": False, "official_website_acceptance": False,
        "proof_compiler_export_kernel_network_runs_by_collector": 0}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
