"""One byte-only archive of the explicitly stopped redundant native-v4 attempt.

No compiler, generator, exporter, kernel, network, Git, or mathematics is run.
The full-PASS material collector is deliberately not imported or executed.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
MIRROR = ROOT / 'tmp/current-s1r-tiny-20261018/production-v2'
FLAT = ROOT / 'research-goal-20261019-tiny-flatten-preparation-v4'
STOP = ROOT / 'research-goal-20261016/gates/tiny-native-v4-stop-after-official-v3-20261019.json'
ACCEPTED = ROOT / 'research-goal-20261019-record-accepted-independent-1753'
COLLECTOR = ROOT / 'research-goal-20261019-native-materials-preparation/prepared-files.json'
EXPECTED = {
    str(STOP): 'e124a5758e1daae1a407bca3826060ef908d4fc0045d3d175ad351bde8da208c',
    str(MIRROR / 'failure.json'): 'f2aafa927830b45008cdbf4ea3e210ed1474cbe91d885fdf1abda394585410b1',
    str(ACCEPTED / 'files.json'): '71f1ba7aaf1ba70b0edf1526103bdf0f1684a4b9c06fbcde3ac5e8a3edb0ebf2',
    str(ACCEPTED / 'accepted-files.json'): 'c528b3b8a5646fe36d924721c5a61ee3193382764dd98cdfa58932f3b2e4b652',
    str(COLLECTOR): '4c9239ec89cbef146a71c18d44e341eca38bda9592a7c92febd2ce1720fef349',
}

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as handle:
        for block in iter(lambda: handle.read(1048576), b''):
            h.update(block)
    return h.hexdigest()

def load(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))

def write_new(path, value):
    with Path(path).open('x', encoding='utf-8', newline='\n') as handle:
        json.dump(value, handle, ensure_ascii=False, indent=2); handle.write('\n')

def row(path):
    return {'path': Path(path).relative_to(ROOT).as_posix(),
            'bytes': Path(path).stat().st_size, 'sha256': sha(path)}

def main():
    assert __debug__ and sys.argv[1:] == ['--archive-cancelled-once']
    assert not (HERE / 'files.json').exists() and not (HERE / 'evidence').exists()
    for path, expected in EXPECTED.items():
        assert sha(path) == expected, path
    stop, failure = load(STOP), load(MIRROR / 'failure.json')
    assert stop['secondary_session'] == 84529 and stop['sole_owner'] == '/root'
    assert stop['official_status'] == 'kernel-verified' and stop['formalVerification'] is True
    assert stop['secondary_run_is_not_a_mathematical_failure_or_a_full_PASS'] is True
    assert failure['failed'] is True and failure['local_single_file_verified'] is False
    assert failure['retry_count'] == 0 and failure['stage'] == 'comparator-default-kernel'
    assert failure['error_type'] == 'KeyboardInterrupt' and failure['error'] == 'Received signal 15'
    assert failure['ordinary_single_file_lean_passed'] is True
    stages = failure['stages']
    assert [stage['label'] for stage in stages] == ['compiler-version', 'generation',
        'ordinary-ChallengeDeps', 'ordinary-ChallengeDeps.CandidateSpec',
        'ordinary-Challenge.Candidate', 'ordinary-Solution.Candidate',
        'challenge-export', 'solution-export', 'comparator-default-kernel']
    assert all(stage['exit_code'] == 0 for stage in stages[:-1])
    assert stages[-1]['exit_code'] == -15
    assert not (MIRROR / 'terminal.json').exists()
    assert not (ROOT / 'submission/single-exception-overlap-native-v4-20261019').exists()
    metadata_path, generation_path = FLAT / 'draft/candidate-metadata.json', FLAT / 'draft/generation.json'
    source = FLAT / 'draft/Solution.lean'
    metadata, generation = load(metadata_path), load(generation_path)
    assert sha(source) == metadata['solution_sha256'] and source.stat().st_size == metadata['solution_bytes']
    assert generation['files'] == [
        {'path': 'Solution.lean', 'bytes': source.stat().st_size, 'sha256': sha(source)},
        {'path': 'candidate-metadata.json', 'bytes': metadata_path.stat().st_size, 'sha256': sha(metadata_path)}]
    assert metadata['upload_ready'] is False
    original_source = row(source)
    inputs = [Path(path) for path in EXPECTED] + [source, metadata_path, generation_path]
    pid_receipt = MIRROR / 'windows-generator.pid.json'
    if pid_receipt.is_file():
        inputs.append(pid_receipt)
    pins = [row(path) for path in inputs]
    copies = [(MIRROR / 'failure.json', 'production-v2.failure.json'),
              (STOP, 'root-stop-gate.json'),
              (metadata_path, 'generation/candidate-metadata.json'),
              (generation_path, 'generation/generation.json')]
    if pid_receipt.is_file():
        copies.append((pid_receipt, 'generation/windows-generator.pid.json'))
    (HERE / 'evidence').mkdir()
    for path, relative in copies:
        assert path.stat().st_size <= 2_000_000
        target = HERE / 'evidence' / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        with path.open('rb') as source_handle, target.open('xb') as target_handle:
            target_handle.write(source_handle.read())
        assert sha(target) == sha(path) and target.stat().st_size == path.stat().st_size
    write_new(HERE / 'status.json', {
        'schema': 'native-v4-superseded-cancellation-v1',
        'archived_at_utc': datetime.now(timezone.utc).isoformat(),
        'status': 'cancelled_as_redundant_after_authoritative_v3_acceptance',
        'production_session_id': 84529,
        'root_reported_real_session_terminal_exit_code': 1,
        'terminal_exit_code_basis': 'Direct sole-owner root report; no invented raw terminal tool result',
        'root_reported_stop_signal': 15,
        'archived_failure_stage': failure['stage'],
        'archived_failure_error_type': failure['error_type'],
        'archived_failure_error': failure['error'],
        'archived_active_child_exit_code': stages[-1]['exit_code'],
        'ordinary_four_module_chain_completed': True,
        'native_challenge_and_solution_exports_completed': True,
        'Comparator_default_kernel_completed': False,
        'nanoda_started': False,
        'full_local_verification_PASS': False,
        'mathematical_counterexample_or_refutation': False,
        'retry_count': 0,
        'automatic_restart_or_retry_requested': False,
        'post_PASS_collector_executions': 0,
        'post_PASS_collector_prepared_sha256': EXPECTED[str(COLLECTOR)],
        'post_PASS_collector_cannot_be_used_for_this_exit1_attempt': True,
        'native_v4_submitted': False,
        'native_v4_official_website_acceptance': False,
        'native_v4_source_reference_only': original_source,
        'native_v4_source_modified_or_overwritten': False,
        'accepted_v3': {
            'id': stop['official_accepted_id'], 'status': stop['official_status'],
            'formalVerification': True, 'source_sha256': stop['official_source_SHA256'],
            'user_job_digest': stop['official_user_job_digest'],
            'evidence_manifest': str((ACCEPTED / 'accepted-files.json').relative_to(ROOT)).replace('\\', '/'),
            'evidence_manifest_sha256': EXPECTED[str(ACCEPTED / 'accepted-files.json')],
            'authoritative_acceptance_is_of_v3_not_this_cancelled_v4': True},
        'Linux_logs_fetched': False,
        'large_NDJSON_oleans_ELF_or_cache_copied': False,
        'compiler_generator_exporter_kernel_network_Git_mathematics_runs_in_archive': 0})
    assert pins == [row(path) for path in inputs], 'An archive dependency or original source changed'
    files = [row(path) for path in sorted(HERE.rglob('*')) if path.is_file()]
    write_new(HERE / 'files.json', {
        'schema': 'native-v4-superseded-evidence-files-v1',
        'scope': 'Byte-only archive of the legitimately cancelled redundant attempt; not a proof PASS',
        'files': files, 'read_dependencies': pins,
        'all_inputs_and_native_v4_source_unchanged': True,
        'cancelled': True, 'full_local_verification_PASS': False,
        'mathematical_counterexample_or_refutation': False, 'retry_count': 0,
        'native_v4_submitted': False, 'native_v4_official_website_acceptance': False,
        'post_PASS_collector_executions': 0})
    print(json.dumps({'archive_created': True, 'manifest_sha256': sha(HERE / 'files.json'),
        'failure_sha256': EXPECTED[str(MIRROR / 'failure.json')],
        'native_v4_source_sha256': original_source['sha256'],
        'cancelled': True, 'full_local_verification_PASS': False, 'retry_count': 0}))

if __name__ == '__main__':
    main()
