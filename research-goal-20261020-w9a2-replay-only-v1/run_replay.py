"""Gated mathematical replay of exact existing exports. Not a cold full-chain run.

Preparation only. Never invokes candidate ordinary compilation or an exporter.
The original failed fullchain-v2 and its 3200-second failure remain unchanged.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import sys
import time
import types

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
BUDGET = 3200.0
OLD_RUNNER_SHA = '92cc8dcf3e3c46e76490ba7bfe8d93bc10e331131eaab3b4c3ae500f80ac66a8'
SOURCE_SHA = 'a517df6aebde6d136f8b83e06c8be10b3413b8430390f52bd47f04e06f0dce26'
CORE_SHA = '7e88e84d1d35d5f3115c97a574cc64dd089ef713ef6f9bccb2303fbd41e07ff2'
ALLOWED = ['propext', 'Quot.sound', 'Classical.choice']
TARGETS = ['candidate_strict_improvement', 'candidate_critical_line_bound', 'candidate_critical_line_bound_cumulative']
NANO_CONFIG = dict(use_stdin=True, permitted_axioms=ALLOWED, unpermitted_axiom_hard_error=True,
    nat_extension=True, string_extension=True, num_threads=0, unsafe_permit_all_axioms=False,
    print_success_message=True, print_axioms=True, pp_to_stdout=True)
ROOTS = ['StructuralW9A220261020.Counting.' + n for n in ['sum_range_coboundary_lower',
    'summed_of_state', 'actual_defect_estimate_effective', 'actual_dyadic_of_summed', 'actual_cumulative_of_summed']] + [
    'StructuralW9A220261020.Localization.located_state', 'StructuralW9A220261020.Graph.edge_from_locations',
    'StructuralW9A220261020.Graph.edge_potential', 'StructuralW9A220261020.Final.actual_summed',
    'StructuralW9A220261020.Final.strict_improvement', 'StructuralW9A220261020.Final.actual_dyadic',
    'StructuralW9A220261020.Final.actual_cumulative', *TARGETS]
RUNTIME_ROLES = {'current-matching-actual-Python-loaded-module', 'installed-Python-controller-library-file',
    'actual-or-ordinary-import-runtime-file', 'actual-application-PE-closure', 'OS-API-set-boundary',
    'ELF-loader-or-launcher-runtime', 'source-bound-interpreted-tool-cache',
    'actual-historical-tool-source-path', 'pinned-trusted-tool-source',
    'Nano-pinned-Cargo-source', 'Nano-dependency-lock', 'Nano-fixed-commit-source'}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def zero(value):
    return type(value) is int and value == 0


def load(path):
    return json.loads(Path(path).read_bytes())


def absolute(value):
    p = Path(value)
    return Path(os.path.abspath(p if p.is_absolute() else ROOT / p))


def plain_sha(path, deadline):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda: f.read(1048576), b''):
            require(time.monotonic() < deadline, 'Replay-only deadline expired during bootstrap pins')
            h.update(b)
    return h.hexdigest()


def setup(a, args):
    gpath = a.bind(args.gate, args.gate_sha256)
    g = a.gate = load(gpath)
    require(g['schema'] == 'w9a2-mathematical-replay-only-gate-v1' and g['sole_owner'] == '/root' and
        g['allow_replay_execution'] is True and g['proposal_only'] is False and
        g['total_budget_seconds'] == BUDGET and zero(g['candidate_ordinary_compiler_runs']) and
        zero(g['exporter_runs']) and zero(g['automatic_retries']) and zero(g['automatic_repairs']), 'Replay gate is disabled or wrong scope')
    proposal = load(HERE / 'gate-proposal.json')
    normalized = dict(g, allow_replay_execution=False, proposal_only=True)
    require(normalized == proposal, 'Enabled gate may only change the two authorization booleans')
    manifest = a.bind(HERE / 'files.json', args.preparation_manifest_sha256)
    for row in load(manifest)['files']:
        p = absolute(HERE / row['path'])
        require(p.is_relative_to(HERE), 'Preparation manifest escape')
        a.bind(p, row['sha256'], row['bytes'])
    require(a.sha(__file__) == g['runner_sha256'], 'Replay runner source changed')
    work = absolute(g['work_directory'])
    require(work.is_relative_to(ROOT / 'tmp') and not work.exists(), 'Replay needs a new exclusive work directory')
    work.mkdir(parents=True, exist_ok=False)
    a.work = work
    for n in ['logs', 'home', 'temporary']:
        (a.work / n).mkdir()
    a.receipt.update(gate_path=str(gpath), gate_sha256=args.gate_sha256,
        preparation_manifest_sha256=args.preparation_manifest_sha256)
    a.write_json(a.work / 'started.json', dict(pid=os.getpid(), monotonic_t0=a.t0,
        total_budget_seconds=BUDGET, gate_sha256=args.gate_sha256, mathematical_replay_only=True,
        cold_full_3200s_passed=False, official_website_acceptance=False))
    oldgate = load(a.bind_row(g['original_gate']))
    archive_manifest = a.bind_row(g['original_failed_archive'])
    archive = archive_manifest.parent
    archive_data = load(archive_manifest)
    for row in archive_data['files']:
        p = absolute(archive / row['path'])
        require(p.is_relative_to(archive), 'Original archive manifest escape')
        a.bind(p, row['sha256'], row['bytes'])
    parent = load(archive / 'root-parent-exit-attestation.json')
    raw = load(archive / 'original-parent-exit.json')
    failure = load(archive / 'job/failure.json')
    require(parent['exec_session_id'] == 68962 and parent['parent_pid'] == 49320 and
        type(parent['actual_exit_code']) is int and parent['actual_exit_code'] == 1 and
        parent['observed_scope'] == 'completed-outer-parent-handle' and
        raw['session'] == 68962 and raw['parent_pid'] == 49320 and
        type(raw['actual_original_handle_result']['exit_code']) is int and raw['actual_original_handle_result']['exit_code'] == 1,
        'Original actual outer exit1 is missing')
    require(failure['failed'] is True and failure['local_fullchain_verified'] is False and
        failure['error_type'] == 'TimeoutExpired' and failure['stage'] == 'comparator-default-Lean-kernel' and
        failure['elapsed_at_failure_seconds'] >= 3200 and failure['ordinary_single_file_passed'] is True and
        failure['source_sha256'] == SOURCE_SHA and failure['source_bytes'] == 1830052,
        'Original failure was not the completed ordinary/export timeout case')
    modules = failure['compiled_modules']
    require([r['module'] for r in modules] == ['ChallengeDeps', 'ChallengeDeps.CandidateSpec', 'Challenge.Candidate', 'Solution.Candidate'] and
        all(zero(r['exit_code']) for r in modules) and modules[-1]['source_sha256'] == SOURCE_SHA,
        'Original four ordinary compilations were not complete')
    axioms = failure['ordinary_printed_axioms']
    require(set(axioms) == set(ROOTS) and all(set(v) <= set(ALLOWED) for v in axioms.values()), 'Original 15 printed axiom roots differ')
    a.receipt.update(original_outer_exit_code=1, original_session=68962, original_parent_pid=49320,
        original_failure_type='TimeoutExpired', original_cold_full_3200s_passed=False,
        original_four_ordinary_compilations_passed=True, original_printed_axioms=axioms,
        source_sha256=SOURCE_SHA, source_bytes=1830052)
    source = a.bind_row(g['source'])
    frozen_source = a.bind_row(g['frozen_source'])
    require(a.sha(source) == SOURCE_SHA and source.stat().st_size == 1830052 and
        source.read_bytes() == frozen_source.read_bytes(), 'Exact existing source changed')
    a.exports = {}
    for label, row in g['existing_exports'].items():
        terminal = load(archive / ('job/logs/' + label + '-native-export.terminal.json'))
        stages = [r for r in failure['stages'] if r['label'] == label + '-native-export']
        require(zero(terminal['exit_code']) and terminal['output_sha256'] == row['sha256'] and
            terminal['output_bytes'] == row['bytes'] and absolute(terminal['output']) == absolute(row['path']) and
            terminal['label'] == label + '-native-export' and len(stages) == 1 and stages[0] == terminal and
            terminal['argv'][1] == ('Challenge.Candidate' if label == 'challenge' else 'Solution.Candidate') and
            terminal['argv'][2] == '--' and terminal['argv'][3:6] == TARGETS,
            'Existing export lacks its genuine completed stage')
        p = a.bind_row(row)
        a.exports[label] = p
    require(set(a.exports) == {'challenge', 'solution'}, 'Exactly two existing exports are required')
    runtime = g['runtime']
    require(runtime == {k: oldgate['runtime'][k] for k in runtime}, 'Replay runtime differs from original checked runtime')
    closure_path = a.bind_row(g['runtime_closure'])
    closure = load(closure_path)
    require(closure['complete_source_bound_runtime_closure_verified'] is True and
        closure['user_proofs_compiled_or_reused_in_setup'] is False and closure['coreaudit_source_sha256'] == CORE_SHA and
        closure['tool_commits'] == g['tool_commits'], 'Original complete source-bound runtime receipt differs')
    a.bind_row(closure['trusted_setup_receipt'])
    sdk = absolute(runtime['lean_sysroot'])
    sdk_prefix = str(sdk).casefold() + os.sep
    selected = {}
    sdk_count = 0
    nano_path = absolute(runtime['nanoda']['host_binary']['path'])
    direct_paths = {absolute(runtime[k]['path']) for k in
        ['lean', 'python_controller', 'wsl_executable', 'taskkill_executable']} | {nano_path}
    for row in closure['files']:
        p = absolute(row['path'])
        is_sdk = str(p).casefold().startswith(sdk_prefix)
        wanted = is_sdk or row.get('role') in RUNTIME_ROLES or p in direct_paths
        # Linux execution aliases are covered by their exact Windows host file.
        if not wanted or row['path'].startswith('/mnt/'):
            continue
        if is_sdk:
            sdk_count += 1
        key = str(p).casefold()
        require(key not in selected, 'Duplicate selected runtime path')
        selected[key] = row
        # Byte hashes bind the selected files. Resolve SDK alias once below,
        # rather than calling Path.resolve for each of 17万 package files.
        a.bind(p, row['sha256'], row['bytes'])
    require(sdk_count == 13951, 'Conservative complete official SDK selection changed')
    a.resolutions[str(sdk)] = str(sdk.resolve())
    a.tool_libs = [absolute(p) for p in runtime['interpreted_tool_libs']]
    require([str(p) for p in a.tool_libs] == closure['interpreted_tool_libs'] and len(a.tool_libs) == 1, 'Wrong trusted tool overlay')
    expected = {'Comparator.olean', 'Comparator/Axioms.olean', 'Comparator/Compare.olean', 'Comparator/Util.olean', 'Export/Parse.olean'}
    require({p.relative_to(a.tool_libs[0]).as_posix() for p in a.tool_libs[0].rglob('*') if p.is_file()} == expected, 'Tool overlay contains an extra module')
    for rel in expected:
        require(str(a.tool_libs[0] / rel).casefold() in selected, 'A tool olean is absent from the verified subset')
    for key in ['lean', 'python_controller', 'wsl_executable', 'taskkill_executable']:
        row = runtime[key]
        p = absolute(row['path'])
        require(str(p).casefold() in selected and selected[str(p).casefold()]['sha256'] == row['sha256'], 'Unbound direct replay executable')
    require(absolute(sys.executable) == absolute(runtime['python_controller']['path']) and
        sys.version == runtime['python_controller']['version'], 'Python controller identity differs')
    require(str(nano_path).casefold() in selected and runtime['nanoda']['host_binary']['sha256'] ==
        'b19804767cb72bf5a317fcfc20e8af7eafdfba789dd6b24bddee2574379ff35a' and
        selected[str(nano_path).casefold()]['sha256'] == runtime['nanoda']['host_binary']['sha256'], 'Pinned Nano differs')
    a.lean = str(absolute(runtime['lean']['path']))
    a.wsl = str(absolute(runtime['wsl_executable']['path']))
    a.taskkill = str(absolute(runtime['taskkill_executable']['path']))
    a.nano = runtime['nanoda']
    a.audit_source = a.bind(g['coreaudit_source']['path'], CORE_SHA)
    a.receipt.update(runtime_selection=dict(selected_files=len(selected), official_SDK_files=sdk_count,
        package_cache_files_rehashed=0, candidate_oleans_imported=False,
        SDK_per_file_Path_resolve_calls=0, original_closure_sha256=g['runtime_closure']['sha256']))
    a.remaining()


def replays(a):
    env = a.environment(a.tool_libs)
    command = [a.lean, '-j1', '-M13500', '--tstack=262144', '--run', str(a.audit_source),
        str(a.exports['challenge']), str(a.exports['solution']), *TARGETS]
    a.receipt['trusted_CoreAudit_lean_run_calls'] = 1
    audit = a.run('comparator-default-Lean-kernel', command, env=env)
    text = a.read_log(audit)
    for message in ['Pinned Comparator statement, dependency and primitive comparison passed',
        'Pinned Comparator transitive axiom check passed', 'Lean default kernel replay passed']:
        require(message in text, 'Full original CoreAudit completion message missing')
    a.receipt.update(Comparator_statement_dependency_primitive_passed=True,
        Comparator_transitive_axioms_passed=True, default_Lean_kernel_replay_passed=True)
    cfg = a.work / 'nanoda-config.json'
    a.write_json(cfg, NANO_CONFIG)
    a.nano_pidfile = a.work / 'nanoda-owned-pgid.txt'
    script = 'umask 077; printf "%s\\n" "$$" > "$1"; exec "$2" "$3"'
    command = a.wsl_command('/usr/bin/setsid', '--wait', '/bin/sh', '-c', script, 'owned-w9a2-replay-nanoda',
        a.linux_mapped(a.nano_pidfile), a.nano['execution_path'], a.linux_mapped(cfg))
    a.receipt['serial_Nano_calls'] = 1
    nano = a.run('serial-nanoda', command, env=env, stdin=a.exports['solution'], wsl_nanoda=True)
    text = a.read_log(nano)
    checked = re.search(r'Checked (\d+) declarations with no errors', text)
    printed = [n.split('.{')[0] for n in re.findall(r'^axiom ([^\s]+)', text, re.M)]
    require(checked is not None and int(checked[1]) > 0 and set(printed) <= set(ALLOWED), 'Complete serial Nano replay failed')
    a.receipt.update(serial_nanoda_passed=True, nanoda_num_threads=0,
        nanoda_checked_declarations=int(checked[1]), nanoda_printed_axioms=printed)


def finish_replay(a):
    a.immutable()
    a.receipt.update(stage='all-mathematical-replay-stages-passed', failed=False,
        mathematical_replay_verified=True, exact_bound_inputs_unchanged=True,
        bound_sha256=dict(a.bound), elapsed_before_final_receipts_seconds=time.monotonic()-a.t0,
        actual_outer_exit0_still_required=True)
    verify = a.work / 'mathematical-replay.json'
    a.write_json(verify, a.receipt, bind=False)
    deadline = a.work / 'deadline-receipt.json'
    a.write_json(deadline, dict(mathematical_replay_sha256=a.sha(verify), total_limit_seconds=BUDGET,
        elapsed_after_fsynced_replay_receipt_seconds=time.monotonic()-a.t0, within_replay_only_limit=True,
        cold_full_3200s_passed=False, official_website_acceptance=False), bind=False)
    terminal = a.work / 'terminal.json'
    a.write_json(terminal, dict(mathematical_replay_sha256=a.sha(verify), deadline_receipt_sha256=a.sha(deadline),
        elapsed_before_terminal_fsync_seconds=time.monotonic()-a.t0, mathematical_replay_completed=True,
        completion_return_code=0, actual_outer_exit0_still_required=True, failure_receipt_must_be_absent=True, cold_full_3200s_passed=False,
        official_website_acceptance=False, submitted=False), bind=False)
    terminal_sha = a.sha(terminal)
    a.remaining()
    print(json.dumps(dict(mathematical_replay_verified=True, work_directory=str(a.work), terminal_sha256=terminal_sha,
        total_elapsed_through_all_fsynced_receipts_seconds=time.monotonic()-a.t0,
        root_must_observe_actual_process_exit_code=0, cold_full_3200s_passed=False,
        official_website_acceptance=False, submitted=False)), flush=True)
    a.remaining()


def main():
    t0 = time.monotonic()
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--gate', required=True)
    ap.add_argument('--gate-sha256', required=True)
    ap.add_argument('--preparation-manifest-sha256', required=True)
    args = ap.parse_args()
    require(__debug__ and os.name == 'nt', 'Use the pinned non-optimized Windows Python controller')
    sys.dont_write_bytecode = True
    oldpath = ROOT / 'research-goal-20261020-w9a2-verification-preparation-v1/run_verification.py'
    require(plain_sha(oldpath, t0+BUDGET) == OLD_RUNNER_SHA, 'Delegated audited runner changed')
    # Execute only this exact already-reviewed Python source, with no pyc cache.
    # Its __main__ guard is false. None of execute/ordinary/proof_replays/finish
    # is called; only its process/deadline/IO/environment methods are reused.
    old = types.ModuleType('pinned_w9a2_process_methods')
    old.__file__ = str(oldpath)
    exec(compile(oldpath.read_bytes(), str(oldpath), 'exec'), old.__dict__)
    a = old.Attempt(t0, args)
    a.receipt = dict(schema='w9a2-mathematical-replay-only-v1', sole_owner='/root',
        started_at_utc=datetime.now(timezone.utc).isoformat(), monotonic_t0=t0, budget_seconds=BUDGET,
        scope='Existing exact exports; separate mathematical replay only; original cold fullchain-v2 failed',
        stages=[], failed=False, mathematical_replay_verified=False, candidate_ordinary_compiler_runs=0,
        exporter_runs=0, trusted_CoreAudit_lean_run_calls=0, serial_Nano_calls=0,
        automatic_retries=0, automatic_repairs=0, existing_exports_reused=True,
        cold_full_3200s_passed=False, official_website_acceptance=False, submitted=False)
    a.bind(oldpath, OLD_RUNNER_SHA)
    def interrupted(signum, frame):
        raise KeyboardInterrupt('Received signal '+str(signum))
    signal.signal(signal.SIGTERM, interrupted)
    try:
        setup(a, args)
        replays(a)
        finish_replay(a)
    except BaseException as error:
        a.receipt.update(mathematical_replay_verified=False, cold_full_3200s_passed=False)
        a.failure(error)
        raise
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
