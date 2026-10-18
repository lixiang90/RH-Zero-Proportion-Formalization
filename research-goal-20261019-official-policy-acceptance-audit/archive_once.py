"""Decode/read official source bytes only; never execute fetched scripts."""
import base64
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
REF = '6bc7f07fb939e066ac2923493d9a01cca553fe87'
RECORD = 'lixiang90-single-exception-overlap-20261018'

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def write_new(path, value):
    with Path(path).open('x', encoding='utf-8', newline='\n') as handle:
        json.dump(value, handle, ensure_ascii=False, indent=2); handle.write('\n')

def row(path):
    return {'path': path.relative_to(ROOT).as_posix(), 'bytes': path.stat().st_size, 'sha256': sha(path)}

def main():
    assert __debug__ and sys.argv[1:] == ['--archive-readonly-sources-once']
    assert not (HERE / 'snapshot').exists() and not (HERE / 'files.json').exists()
    transport_path = HERE / 'github-transport.json'
    original_transport = sha(transport_path)
    transport = json.loads(transport_path.read_text(encoding='utf-8'))
    assert len(transport['files']) == 5
    sources = {}
    provenance = []
    for fetched in transport['files']:
        request, response = fetched['request'], fetched['response']
        assert request['repository_full_name'] == 'josusanmartin/riemann' and request['ref'] == REF
        assert request['encoding'] == response['encoding'] == 'base64'
        name = request['path']
        assert not Path(name).is_absolute() and '..' not in Path(name).parts
        data = base64.b64decode(''.join(response['content'].split()), validate=True)
        assert len(data) < 1_000_000, 'Only small source/log artifacts are archived'
        blob_id = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        assert blob_id == response['sha'], name
        target = HERE / 'snapshot' / name
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as handle:
            handle.write(data)
        assert target.read_bytes() == data
        sources[name] = data.decode('utf-8')
        provenance.append({'request': request, 'GitHub_blob_sha1': blob_id,
            'blob_sha1_recomputed_match': True, 'bytes': len(data), 'sha256': sha(target),
            'display_url': response['display_url'], 'saved_path': target.relative_to(ROOT).as_posix()})
    inner = sources['scripts/run-comparator-e2b.sh']
    outer = sources['e2b/run-verification-job.sh']
    contributing = sources['CONTRIBUTING.md']
    assert 'exec timeout --signal=TERM --kill-after=15s 3200s' in inner
    assert 'timeout --signal=TERM --kill-after=15s 3240s' in outer
    assert '--mode=full' in outer
    assert 'COMPARATOR_BIN=/opt/riemann/tools/bin/comparator' in outer
    assert 'COMPARATOR_LEAN4EXPORT=/opt/riemann/tools/bin/lean4export' in outer
    assert 'COMPARATOR_NANODA=/opt/riemann/tools/bin/nanoda_bin' in outer
    assert 'Lean accepts the exported proof.' in contributing
    assert 'The independent nanoda kernel accepts the proof.' in contributing
    assert 'candidate-controlled hypotheses' in contributing
    artifact_root = 'submissions/' + RECORD + '/verification/'
    attestation = json.loads(sources[artifact_root + 'attestation.json'])
    log = sources[artifact_root + 'verifier.log']
    assert attestation['submissionId'] == RECORD and attestation['result'] == 'kernel-verified'
    assert attestation['kernels'] == ['lean', 'nanoda']
    assert set(attestation['permittedAxioms']) == {'propext', 'Quot.sound', 'Classical.choice'}
    assert attestation['score'] == {
        'numerator': '3337839448633819172184136761695440236797',
        'denominator': '4955319193827760237900000000000000000000'}
    for phrase in ['Building Challenge.Candidate', 'Building Solution.Candidate',
        'Exporting #[Nat, String', 'Nanoda kernel accepts the solution',
        'Lean default kernel accepts the solution', 'Your solution is okay!']:
        assert phrase in log, phrase
    assert re.search(r'Built Solution\.Candidate \(', log)
    assert log.index('Nanoda kernel accepts the solution') < log.index('Lean default kernel accepts the solution')
    def line_hits(name, terms):
        return [{'line': index, 'text': line} for index, line in enumerate(sources[name].splitlines(), 1)
                if any(term in line for term in terms)]
    report = {
        'schema': 'official-policy-and-accepted-runtime-evidence-audit-v1',
        'audited_at_utc': datetime.now(timezone.utc).isoformat(),
        'repository': 'josusanmartin/riemann', 'accepted_source_commit': REF,
        'all_five_files_fetched_at_exact_same_commit': True,
        'transport': 'GitHub connector fetch_file base64; each Git blob SHA1 recomputed from raw decoded bytes',
        'official_public_verification_artifacts_found': True,
        'search_default_branch_ref_is_not_used_as_a_substitute_for_exact_commit_fetch': True,
        'official_attestation': attestation,
        'official_log_confirms_ordinary_solution_build_and_both_kernels': True,
        'ordinary_solution_build_lines': line_hits(artifact_root + 'verifier.log', ['Built Solution.Candidate']),
        'official_kernel_success_lines': line_hits(artifact_root + 'verifier.log', [
            'Nanoda kernel accepts the solution', 'Lean default kernel accepts the solution', 'Your solution is okay!']),
        'official_policy': {
            'comparator_main_timeout_seconds': 3200,
            'outer_E2B_full_job_timeout_seconds': 3240,
            'TERM_then_kill_after_seconds': 15,
            'inner_scope': 'Comparator main launched via lake env; not an assertion that all outer job setup belongs to the inner 3200 seconds',
            'full_mode_explicit': True,
            'native_comparator_exporter_nanoda_paths_explicit': True,
            'source_lines': {
                'inner': line_hits('scripts/run-comparator-e2b.sh', ['ulimit -f', 'exec timeout', 'lake env']),
                'outer': line_hits('e2b/run-verification-job.sh', ['3240s', 'COMPARATOR_BIN=', 'COMPARATOR_LEAN4EXPORT=', 'COMPARATOR_NANODA=', '--mode=full'])}},
        'elapsed_time_limits': {
            'precise_total_elapsed_seconds_published_in_attestation': False,
            'precise_total_elapsed_seconds_claimed': None,
            'individual_Lake_build_times_are_not_total_pipeline_elapsed': True,
            'policy_timeout_is_not_an_observed_stopwatch_measurement': True},
        'attestation_upstreamCommit': attestation.get('upstreamCommit'),
        'upstream_ref_lookup_note': 'Additional fetches of the attestation upstreamCommit in josusanmartin/riemann returned no-such-commit 404. It is not asserted to identify this repository pipeline revision. The five archived official files are independently pinned to the exact accepted-source commit above.',
        'Challenge_template_sorry_warning_note': 'The log warns about sorry in trusted Challenge.Candidate placeholders; this is the statement comparison template. The accepted Solution public theorems were built and accepted by both kernels, and the formal permitted-axiom list is the standard three.',
        'source_scripts_executed': 0,
        'compiler_generator_exporter_kernel_mathematics_or_website_submission_runs': 0}
    write_new(HERE / 'provenance.json', {'schema': 'official-file-byte-provenance-v1', 'files': provenance})
    write_new(HERE / 'audit.json', report)
    assert sha(transport_path) == original_transport
    files = [row(path) for path in sorted(HERE.rglob('*')) if path.is_file()]
    write_new(HERE / 'files.json', {'schema': 'official-policy-acceptance-audit-files-v1',
        'files': files, 'source_scripts_executed': 0,
        'compiler_network_math_or_submission_executed_by_archive_script': 0,
        'GitHub_read_only_source_fetches_preceded_archive': True,
        'exact_commit': REF, 'public_attestation_and_verifier_log_found': True,
        'both_kernel_acceptance_confirmed': True})
    print(json.dumps({'manifest_sha256': sha(HERE / 'files.json'), 'file_count': len(files),
        'public_attestation_and_verifier_log_found': True, 'both_kernel_acceptance_confirmed': True,
        'source_scripts_executed': 0}))

if __name__ == '__main__':
    main()
