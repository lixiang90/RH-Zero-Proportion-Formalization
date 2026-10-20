"""Future metadata-only collector; not executed during preparation.

Accepts only the original83153 mathematical replay's real outer exit0.
Preserves original cold fullchain-v2 failure; never invokes a proof tool.
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
WORK = ROOT / "tmp/w9a2-20261020/replay-only-v1"
ORIGINAL = ROOT / "research-goal-20261020-w9a2-fullchain-v2-terminal"
ORIGINAL_WORK = ROOT / "tmp/w9a2-20261020/fullchain-v2"
PREPARED = ROOT / "submission/w9a2-weighted-potential-20261020-prepared-v6"
WIRE = ROOT / "submission/w9a2-weighted-potential-20261020-expected-wire-v6"
REPLAY_PACK = ROOT / "research-goal-20261020-w9a2-replay-only-v1"
DEST = ROOT / "submission/w9a2-weighted-potential-20261020-math-verified-v1"
SOURCE_SHA = "a517df6aebde6d136f8b83e06c8be10b3413b8430390f52bd47f04e06f0dce26"
RUNNER_SHA = "f9048bc8bb320a895894df4aaf2d82a6b1e5b79b4da05600fb9184330237791c"
GATE_SHA = "587b70dce4265c72679ffa4988d12004ae42a9f22b9398a1cb33a045c3476e70"
PREPARED_SHA = "55c28b9f90515324f40144822d9e84b301fe9001ec1a03e8df2bf1350159522f"
WIRE_SHA = "f81666062165a2a1e60bd59b88cedcc237e72bebe9faca0f183b021fec636851"
OLD_ARCHIVE_SHA = "ae3eb7e1a907199639e3d054750c263315e303215a633cdb4c2eec96e10e5169"
REPLAY_PACK_SHA = "d5552f25ba8b77332ff275b931b529d5e771456663950da90fc6a69348622ade"
SERVER_SHA = "e9aace57386e2bbf5ef9db3ad4bb8585db7173b315141b13bee6b1646bd00ec2"
WIRE_DIGEST = "e76462f687d4e95d7f9f2ebb558bd5d2d5452814f01e54fd657856dbb12157d1"
CORE_SHA = "7e88e84d1d35d5f3115c97a574cc64dd089ef713ef6f9bccb2303fbd41e07ff2"
ALLOWED = ["propext", "Quot.sound", "Classical.choice"]
TARGETS = ["candidate_strict_improvement", "candidate_critical_line_bound", "candidate_critical_line_bound_cumulative"]
CONFIG = dict(use_stdin=True, permitted_axioms=ALLOWED, unpermitted_axiom_hard_error=True,
    nat_extension=True, string_extension=True, num_threads=0, unsafe_permit_all_axioms=False,
    print_success_message=True, print_axioms=True, pp_to_stdout=True)
EXPORTS = {"challenge": (349332110, "a292e2fc44e0b69bcfaad53175bbeb1cda71b14b1edaab4bb779160f949bc6d0"),
    "solution": (677296932, "1cc0f929919e0d4f58d947223c75a82450df57da11a9fe43fd93a90d8c8433d7")}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def zero(value):
    return type(value) is int and value == 0


def numeric(value):
    return type(value) in (int, float) and math.isfinite(value)


def path(value):
    item = Path(value)
    item = (item if item.is_absolute() else ROOT / item).resolve()
    require(item.is_relative_to(ROOT.resolve()), "Evidence path leaves workspace")
    return item


def sha(item):
    digest = hashlib.sha256()
    with Path(item).open("rb") as source:
        for block in iter(lambda: source.read(1048576), b""):
            digest.update(block)
    return digest.hexdigest()


def load(item):
    return json.loads(Path(item).read_bytes())


class Pins:
    def __init__(self):
        self.rows = {}

    def current(self, value, digest=None, size=None):
        item = path(value)
        require(item.is_file(), "Missing completed evidence: " + str(item))
        row = {"path": item.relative_to(ROOT.resolve()).as_posix(), "bytes": item.stat().st_size, "sha256": sha(item)}
        require(digest is None or digest == row["sha256"], "SHA mismatch: " + str(item))
        require(size is None or size == row["bytes"], "Size mismatch: " + str(item))
        require(str(item) not in self.rows or self.rows[str(item)] == row, "Evidence changed between reads")
        self.rows[str(item)] = row
        return item

    def row(self, row):
        return self.current(row["path"], row["sha256"], row.get("bytes"))

    def manifest(self, folder, digest):
        item = self.current(folder / "files.json", digest)
        data = load(item)
        for row in data["files"]:
            target = path(folder / row["path"])
            require(target.is_relative_to(folder.resolve()), "Manifest path escape")
            self.current(target, row["sha256"], row["bytes"])
        return data

    def immutable(self):
        for filename, row in self.rows.items():
            require(path(filename) == Path(filename) and Path(filename).stat().st_size == row["bytes"] and sha(filename) == row["sha256"],
                "Input changed during collection")


def write(relative, raw):
    item = DEST / relative
    item.parent.mkdir(parents=True, exist_ok=True)
    with item.open("xb") as output:
        output.write(raw); output.flush(); os.fsync(output.fileno())


def dump(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def copy(relative, source, pins):
    raw = source.read_bytes(); row = pins.rows[str(source.resolve())]
    require(len(raw) == row["bytes"] and hashlib.sha256(raw).hexdigest() == row["sha256"], "Evidence changed before copy")
    write(relative, raw)


def mapped(item):
    item = path(item)
    require(re.fullmatch("[A-Za-z]:", item.drive) is not None, "Expected local Windows drive")
    return "/mnt/" + item.drive[0].lower() + str(item)[2:].replace("\\", "/")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--outer-observation", required=True)
    parser.add_argument("--outer-observation-sha256", required=True)
    parser.add_argument("--preparation-manifest-sha256", required=True)
    args = parser.parse_args()
    require(__debug__ and not DEST.exists(), "Use non-optimized Python and a nonexistent new destination")
    pins = Pins(); pins.manifest(HERE, args.preparation_manifest_sha256)
    require(str(path(__file__)) in pins.rows, "Collector source absent from preparation manifest")
    prepared = pins.manifest(PREPARED, PREPARED_SHA); wire = pins.manifest(WIRE, WIRE_SHA)
    require(len(prepared["files"]) == 13 and {row["path"] for row in wire["files"]} == {"expected-server-submission.json", "prediction.json"},
        "Frozen prepared/wire scope changed")
    pins.manifest(REPLAY_PACK, REPLAY_PACK_SHA)
    runner = pins.current(REPLAY_PACK / "run_replay.py", RUNNER_SHA)
    source = pins.current(PREPARED / "proof/Solution.lean", SOURCE_SHA, 1830052)
    original_source = pins.current(ORIGINAL_WORK / "source/Solution/Candidate.lean", SOURCE_SHA, 1830052)
    require(source.read_bytes() == original_source.read_bytes(), "Original exact source changed")
    require(not (WORK / "failure.json").exists(), "Replay failure receipt exists")
    start_path = pins.current(WORK / "started.json"); started = load(start_path)
    require(started["pid"] == 15012 and started["monotonic_t0"] == 15521.156 and started["gate_sha256"] == GATE_SHA and
        started["total_budget_seconds"] == 3200 and started["mathematical_replay_only"] is True and started["cold_full_3200s_passed"] is False,
        "Wrong original replay start")
    replay_path = pins.current(WORK / "mathematical-replay.json"); replay = load(replay_path)
    deadline_path = pins.current(WORK / "deadline-receipt.json"); deadline = load(deadline_path)
    terminal_path = pins.current(WORK / "terminal.json"); terminal = load(terminal_path)
    require(replay["schema"] == "w9a2-mathematical-replay-only-v1" and replay["failed"] is False and replay["mathematical_replay_verified"] is True and
        replay["stage"] == "all-mathematical-replay-stages-passed" and replay["exact_bound_inputs_unchanged"] is True and
        replay["monotonic_t0"] == started["monotonic_t0"] and replay["budget_seconds"] == 3200, "No completed mathematical replay")
    require(replay["source_sha256"] == SOURCE_SHA and replay["source_bytes"] == 1830052 and replay["sole_owner"] == "/root" and
        replay["gate_sha256"] == GATE_SHA and replay["preparation_manifest_sha256"] == REPLAY_PACK_SHA, "Replay source/authorization differs")
    for name in ["candidate_ordinary_compiler_runs", "exporter_runs", "automatic_retries", "automatic_repairs", "nanoda_num_threads"]:
        require(zero(replay[name]), "Forbidden compiler/export/retry/threads scope")
    require(type(replay["trusted_CoreAudit_lean_run_calls"]) is int and replay["trusted_CoreAudit_lean_run_calls"] == 1 and
        type(replay["serial_Nano_calls"]) is int and replay["serial_Nano_calls"] == 1 and replay["existing_exports_reused"] is True,
        "Expected one interpreted trusted Lean run and one serial Nano")
    for name in ["Comparator_statement_dependency_primitive_passed", "Comparator_transitive_axioms_passed", "default_Lean_kernel_replay_passed", "serial_nanoda_passed"]:
        require(replay[name] is True, "A required mathematical replay gate failed")
    require(all(document["cold_full_3200s_passed"] is False and document["official_website_acceptance"] is False for document in [replay, deadline, terminal]) and
        replay["submitted"] is False and terminal["submitted"] is False and not replay.get("local_fullchain_verified", False), "Scope upgraded to cold/official PASS")
    require(deadline["mathematical_replay_sha256"] == terminal["mathematical_replay_sha256"] == sha(replay_path) and
        terminal["deadline_receipt_sha256"] == sha(deadline_path) and deadline["total_limit_seconds"] == 3200 and
        deadline["within_replay_only_limit"] is True and terminal["mathematical_replay_completed"] is True and
        zero(terminal["completion_return_code"]) and terminal["failure_receipt_must_be_absent"] is True and terminal["actual_outer_exit0_still_required"] is True,
        "The three replay receipts are incomplete/unlinked")
    gate_path = pins.current(replay["gate_path"], GATE_SHA); gate = load(gate_path)
    require(dict(gate, allow_replay_execution=False, proposal_only=True) == load(REPLAY_PACK / "gate-proposal.json") and
        gate["allow_replay_execution"] is True and gate["proposal_only"] is False and gate["runner_sha256"] == RUNNER_SHA and
        path(gate["work_directory"]) == WORK.resolve(), "Replay typed gate differs")
    core = pins.row(gate["coreaudit_source"]); require(sha(core) == CORE_SHA, "Locked CoreAudit changed")
    outer_path = pins.current(args.outer_observation, args.outer_observation_sha256); outer = load(outer_path)
    require(outer["schema"] == "w9a2-root-terminal-observation-v1" and outer["sole_owner"] == "/root" and outer["role"] == "replay-only-v1" and
        outer["exec_session_id"] == 83153 and outer["parent_pid"] == 15012 and zero(outer["actual_exit_code"]) and
        outer["observed_scope"] == "completed-outer-parent-handle" and outer["observation_source"] in ["functions.exec_command", "functions.write_stdin"],
        "Original83153 actual root outer exit0 missing")
    require(pins.row(outer["runner"]) == runner and pins.row(outer["completion_receipt"]) == terminal_path, "Outer runner/terminal differs")
    if "gate" in outer:
        require(pins.row(outer["gate"]) == gate_path, "Outer gate differs")
    raw_path = pins.row(outer["raw_tool_terminal"]); raw = load(raw_path)
    require(zero(raw.get("exit_code")) and isinstance(raw.get("output"), str) and raw.get("session_id") in [None, 83153], "No real outer tool exit0/output")
    final_records = []
    for line in raw["output"].splitlines():
        try:
            value = json.loads(line)
        except (ValueError, TypeError):
            continue
        if isinstance(value, dict) and "total_elapsed_through_all_fsynced_receipts_seconds" in value:
            final_records.append(value)
    require(len(final_records) == 1, "No unique final printed receipt hash/time")
    final = final_records[0]
    require(final["mathematical_replay_verified"] is True and final["terminal_sha256"] == sha(terminal_path) and path(final["work_directory"]) == WORK.resolve() and
        zero(final["root_must_observe_actual_process_exit_code"]) and final["cold_full_3200s_passed"] is False and
        final["official_website_acceptance"] is False and final["submitted"] is False, "Actual final hash/scope differs")
    elapsed = [replay["elapsed_before_final_receipts_seconds"], deadline["elapsed_after_fsynced_replay_receipt_seconds"],
        terminal["elapsed_before_terminal_fsync_seconds"], final["total_elapsed_through_all_fsynced_receipts_seconds"]]
    require(all(numeric(value) for value in elapsed) and 0 < elapsed[0] <= elapsed[1] <= elapsed[2] <= elapsed[3] < 3200, "New same-clock3200 chain failed")
    observed = datetime.fromisoformat(outer["observed_at_utc"].replace("Z", "+00:00"))
    began = datetime.fromisoformat(replay["started_at_utc"].replace("Z", "+00:00"))
    require(observed.tzinfo is not None and began.tzinfo is not None and began <= observed <= datetime.now(timezone.utc), "Invalid actual outer observation time")
    stages = replay["stages"]
    require([stage["label"] for stage in stages] == ["comparator-default-Lean-kernel", "serial-nanoda"], "Only two complete replay stages expected")
    current_evidence = [start_path, replay_path, deadline_path, terminal_path, pins.current(WORK / "nanoda-config.json")]
    end = started["monotonic_t0"]
    for stage in stages:
        require(zero(stage["exit_code"]) and type(stage["pid"]) is int and stage["pid"] > 0 and numeric(stage["started_monotonic"]) and
            numeric(stage["elapsed_seconds"]) and stage["elapsed_seconds"] >= 0 and stage["started_monotonic"] >= end and
            0 < stage["remaining_total_budget_seconds"] <= 3200 and path(stage["cwd"]) == WORK.resolve(), "Stage actual process/clock differs")
        end = stage["started_monotonic"] + stage["elapsed_seconds"]
        require(end <= started["monotonic_t0"] + elapsed[-1], "Stage exceeds final replay completion clock")
        log = pins.current(stage["log"], stage["log_sha256"])
        require(log == (WORK / "logs" / (stage["label"] + ".log")).resolve(), "Unexpected actual log path")
        current_evidence.append(log)
        for suffix in ["started", "child", "terminal"]:
            item = pins.current(WORK / "logs" / (stage["label"] + "." + suffix + ".json")); data = load(item)
            require(data == {"pid": stage["pid"], "argv": stage["argv"]} if suffix == "child" else all(stage.get(key) == value for key, value in data.items()),
                "Actual stage metadata differs from full replay receipt")
            current_evidence.append(item)
    expected_audit = [gate["runtime"]["lean"]["path"], "-j1", "-M13500", "--tstack=262144", "--run", str(core),
        str(ORIGINAL_WORK / "challenge.ndjson"), str(ORIGINAL_WORK / "solution.ndjson"), *TARGETS]
    require(path(stages[0]["argv"][0]) == path(expected_audit[0]) and stages[0]["argv"][1:] == expected_audit[1:], "CoreAudit actual command differs")
    audit_log = Path(stages[0]["log"]).read_text("utf-8")
    for message in ["Pinned Comparator statement, dependency and primitive comparison passed", "Pinned Comparator transitive axiom check passed", "Lean default kernel replay passed"]:
        require(message in audit_log, "CoreAudit full completion message missing")
    actual_config = load(WORK / "nanoda-config.json")
    require(actual_config == CONFIG and zero(actual_config["num_threads"]), "Serial Nano exact configuration changed")
    script = 'umask 077; printf "%s\\n" "$$" > "$1"; exec "$2" "$3"'
    expected_nano = [gate["runtime"]["wsl_executable"]["path"], "--distribution", "Ubuntu", "--exec", "/usr/bin/setsid", "--wait", "/bin/sh", "-c", script,
        "owned-w9a2-replay-nanoda", mapped(WORK / "nanoda-owned-pgid.txt"), gate["runtime"]["nanoda"]["execution_path"], mapped(WORK / "nanoda-config.json")]
    require(stages[1]["argv"] == expected_nano and stages[1]["wsl_nanoda"] is True, "Nano command does not wait for real owned child")
    nano_log = Path(stages[1]["log"]).read_text("utf-8")
    checked = re.search(r"Checked (\d+) declarations with no errors", nano_log)
    printed = [name.split('.{')[0] for name in re.findall(r'^axiom ([^\s]+)', nano_log, re.M)]
    require(checked is not None and int(checked[1]) > 0 and type(replay["nanoda_checked_declarations"]) is int and
        int(checked[1]) == replay["nanoda_checked_declarations"] and printed == replay["nanoda_printed_axioms"] and set(printed) <= set(ALLOWED), "Nano full checked-count/axiom log differs")
    archive_manifest = pins.current(ORIGINAL / "files.json", OLD_ARCHIVE_SHA)
    archive_rows = load(archive_manifest)["files"]
    original_evidence = [archive_manifest]
    # Verify only original small evidence. No SDK/cache walk and no candidate
    # recompilation. Original large exports are checked below and left in place.
    for name in ["root-parent-exit-attestation.json", "original-parent-exit.json", "job/failure.json", "retained-binary-and-export-artifacts.json"]:
        item = ORIGINAL / name; row = next(row for row in archive_rows if row["path"] == name)
        original_evidence.append(pins.current(item, row["sha256"], row["bytes"]))
    parent = load(ORIGINAL / "root-parent-exit-attestation.json"); oldraw = load(ORIGINAL / "original-parent-exit.json")
    failure = load(ORIGINAL / "job/failure.json")
    require(parent["exec_session_id"] == oldraw["session"] == 68962 and parent["parent_pid"] == oldraw["parent_pid"] == 49320 and
        type(parent["actual_exit_code"]) is int and parent["actual_exit_code"] == 1 and type(oldraw["actual_original_handle_result"]["exit_code"]) is int and
        oldraw["actual_original_handle_result"]["exit_code"] == 1 and
        failure["error_type"] == "TimeoutExpired" and failure["failed"] is True and failure["local_fullchain_verified"] is False and
        failure["source_sha256"] == SOURCE_SHA and failure["ordinary_single_file_passed"] is True and failure["elapsed_at_failure_seconds"] >= 3200,
        "Original real cold failure evidence changed")
    require(replay["original_session"] == 68962 and replay["original_parent_pid"] == 49320 and replay["original_outer_exit_code"] == 1 and
        replay["original_cold_full_3200s_passed"] is False and replay["original_failure_type"] == "TimeoutExpired" and
        replay["original_four_ordinary_compilations_passed"] is True and replay["original_printed_axioms"] == failure["ordinary_printed_axioms"] and
        len(replay["original_printed_axioms"]) == 15 and set(TARGETS) <= set(replay["original_printed_axioms"]) and
        all(set(value) <= set(ALLOWED) for value in replay["original_printed_axioms"].values()), "Original proof/axiom scope differs")
    export_pins = {}
    for label, (size, digest) in EXPORTS.items():
        item = pins.current(ORIGINAL_WORK / (label + ".ndjson"), digest, size)
        require(gate["existing_exports"][label]["sha256"] == digest and gate["existing_exports"][label]["bytes"] == size, "Reused export gate pin differs")
        export_pins[label] = pins.rows[str(item)]
    # A bound hash is already in the actual replay receipt; do not traverse or
    # rehash its 14k SDK/runtime file entries in this collection step.
    replay_owned_controls = [item for item in current_evidence if item not in [replay_path, deadline_path, terminal_path]]
    for item in [runner, source, original_source, core, *replay_owned_controls, *(path(row["path"]) for row in export_pins.values())]:
        require(replay["bound_sha256"].get(str(item)) == pins.rows[str(item)]["sha256"], "Actual replay did not bind this exact input")
    server = pins.current(WIRE / "expected-server-submission.json", SERVER_SHA); manifest = load(server)
    require(manifest["model"] is None and manifest["harness"] == "Codex" and manifest["author"] == {"github": "lixiang90", "displayName": "Li Xiang"}, "Expected server metadata changed")
    predicted = hashlib.sha256(b"submission.json\0" + server.read_bytes() + b"proof/Solution.lean\0" + source.read_bytes()).hexdigest()
    require(predicted == WIRE_DIGEST == load(WIRE / "prediction.json")["expected_job_proofDigest"], "Expected unchanged wire digest differs")
    pins.immutable(); require(not (WORK / "failure.json").exists(), "Replay failure appeared before collection")
    DEST.mkdir(parents=True, exist_ok=False)
    for row in prepared["files"]:
        copy(row["path"], PREPARED / row["path"], pins)
    copy("evidence/prepared-v6-files.original.json", PREPARED / "files.json", pins)
    for row in wire["files"]:
        copy("expected-wire/" + row["path"], WIRE / row["path"], pins)
    copy("expected-wire/files.json", WIRE / "files.json", pins)
    for item in current_evidence:
        copy("evidence/replay/" + item.relative_to(WORK).as_posix(), item, pins)
    for name, item in [("root-outer-observation.json", outer_path), ("root-raw-tool-terminal.json", raw_path), ("replay-gate.json", gate_path),
        ("run_replay.py", runner), ("CoreAudit.lean", core)]:
        copy("evidence/" + name, item, pins)
    for item in original_evidence:
        copy("evidence/original-v2-reference/" + item.relative_to(ORIGINAL).as_posix(), item, pins)
    addendum = dict(schema="w9a2-actual-mathematical-replay-addendum-v1", source_sha256=SOURCE_SHA, source_bytes=1830052,
        original_replay_session=83153, original_replay_parent_pid=15012, monotonic_t0=15521.156, actual_outer_exit_code=0,
        mathematical_replay_verified=True, Comparator_statement_dependency_primitive_passed=True, Comparator_transitive_axioms_passed=True,
        default_Lean_kernel_replay_passed=True, serial_nanoda_passed=True, nanoda_checked_declarations=replay["nanoda_checked_declarations"],
        separate_replay_budget_seconds=3200, separate_replay_elapsed_through_all_fsynced_receipts_seconds=elapsed[-1],
        original_cold_session=68962, original_cold_actual_exit_code=1, original_cold_failure="TimeoutExpired",
        original_cold_elapsed_seconds=failure["elapsed_at_failure_seconds"], cold_full_3200s_passed=False,
        original_cold_archive_preserved=True, original_archive_manifest=pins.rows[str(archive_manifest)],
        prepared13_files_copied_verbatim=True, prepared_verification_status_is_historical_snapshot=True,
        this_addendum_is_current_mathematical_status=True, current_export_pins=export_pins,
        trusted_CoreAudit_lean_run_calls=1, candidate_ordinary_compiler_runs=0, exporter_runs=0, collector_SDK_runtime_files_rehashed=0,
        input_pins=list(pins.rows.values()), expected_job_proofDigest=predicted, actual_official_observed_proofDigest=None,
        model_UI_field="", expected_server_model=None, fresh_R_check_before_submission_still_required=True,
        submitted=False, official_website_acceptance=False, official_fixed_complete_3200s_accepted=False, official_job_id=None,
        proof_compiler_export_kernel_network_runs_by_collector=0)
    write("mathematical-verification-addendum.json", dump(addendum))
    write("MATHEMATICAL-VERIFICATION.zh.md", ("本包只在原83153/PID15012数学重放真实exit0后生成。三收据、同新时钟3200秒、CoreAudit完整三消息和serialNano完整检查、sourcea517与两原exports当前字节都须核验。\n\n原13份prepared-v6材料逐字保留，是当时的历史状态；当前数学状态见mathematical-verification-addendum.json。可信CoreAudit实际使用一个Lean --run进程，候选普通编译与export均未重跑。\n\n原cold-v2的68962/PID49320真实TimeoutExpired/exit1及3200.578秒失败永久保留；数学重放不能变成原cold3200PASS。原失败完整归档仍在原目录，本包original-v2-reference只复制小型引用证据，不冒称复制整份归档。\n\n官网未提交、未接受；其固定完整3200秒实际接受仍待root另确认。提交前须再查最新精确R、实际wire源码和组合digest。后续官网结果另加hash-linked addendum，不修改原源码或本包。\n").encode())
    files = [{"path": item.relative_to(DEST).as_posix(), "bytes": item.stat().st_size, "sha256": sha(item)} for item in sorted(DEST.rglob("*")) if item.is_file()]
    write("files.json", dump(dict(schema="w9a2-math-verified-evidence-files-v1", source_sha256=SOURCE_SHA, mathematical_replay_verified=True,
        cold_full_3200s_passed=False, submitted=False, official_website_acceptance=False, files=files)))
    print(json.dumps(dict(destination=str(DEST), manifest_sha256=sha(DEST / "files.json"), source_sha256=SOURCE_SHA,
        mathematical_replay_verified=True, cold_full_3200s_passed=False, submitted=False, official_website_acceptance=False,
        proof_compiler_export_kernel_network_runs_by_collector=0)), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
