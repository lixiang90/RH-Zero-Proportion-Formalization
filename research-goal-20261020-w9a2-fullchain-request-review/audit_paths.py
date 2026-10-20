"""Filesystem-only independent request pin scan; no verifier imports/execution.

Writes only this NEW review directory. Does not edit the frozen request, gates,
proof sources, runtime setup, or process state. No subprocess or network API.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
PROPOSAL = ROOT / 'research-goal-20261020-w9a2-fullchain-request-preparation/request-proposal.json'
PROPOSAL_SHA = '02ec0bc362f17cd5f6a7fe53516f4d20306770bc1f20d4b31958b5fd66f88ff9'
PREPARED_SHA = '36fc71d70451747c9028ba7d1e1e7f8599f5fecbdcd6ede3b5a33e1679260656'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
pins = {}
checks = []
pending = []


def absolute(value):
    item = Path(value)
    return item if item.is_absolute() else ROOT / item


def sha(item):
    result = hashlib.sha256()
    with Path(item).open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            result.update(block)
    return result.hexdigest()


def pin(value):
    item = absolute(value)
    before = item.stat()
    result = sha(item)
    after = item.stat()
    assert (before.st_size, before.st_mtime_ns) == (after.st_size, after.st_mtime_ns)
    entry = {'path': str(item), 'resolved_path': str(item.resolve()),
             'bytes': after.st_size, 'sha256': result}
    assert str(item) not in pins or pins[str(item)] == entry
    pins[str(item)] = entry
    return entry


def check(context, value, expected, expected_bytes=None):
    item = absolute(value)
    if not isinstance(expected, str) or re.fullmatch('[0-9a-f]{64}', expected) is None or 'ROOT_MUST' in str(value):
        pending.append({'context': context, 'path': str(value), 'sha256': expected,
                        'status': 'INTENTIONALLY_UNFILLED_NOT_VALIDATED'})
        return None
    if not item.is_file():
        result = {'context': context, 'path': str(value), 'expected_sha256': expected, 'status': 'MISSING'}
    else:
        actual = pin(item)
        ok = actual['sha256'] == expected and (expected_bytes is None or actual['bytes'] == expected_bytes)
        result = {'context': context, 'path': str(value), 'expected_sha256': expected,
                  'expected_bytes': expected_bytes, 'actual': actual, 'status': 'PASS' if ok else 'MISMATCH'}
    checks.append(result)
    return result


def scan(obj, context='$'):
    if isinstance(obj, dict):
        if 'path' in obj and 'sha256' in obj:
            check(context, obj['path'], obj['sha256'], obj.get('bytes'))
        for key, value in obj.items():
            scan(value, context + '.' + key)
    elif isinstance(obj, list):
        for index, value in enumerate(obj):
            scan(value, context + '[' + str(index) + ']')


def manifest(context, file, expected):
    item = absolute(file)
    result = check(context, item, expected)
    assert result['status'] == 'PASS', result
    data = json.loads(item.read_bytes())
    for index, entry in enumerate(data['files']):
        target = item.parent / entry['path']
        assert target.resolve().is_relative_to(item.parent.resolve())
        check(context + '.files[' + str(index) + ']', target, entry['sha256'], entry['bytes'])
    return data


def emit(path, obj):
    with path.open('xb') as stream:
        stream.write((json.dumps(obj, ensure_ascii=False, indent=2) + '\n').encode())


def main():
    check('frozen_request', PROPOSAL, PROPOSAL_SHA)
    manifest('frozen_request_package', PROPOSAL.parent / 'prepared-files.json', PREPARED_SHA)
    request = json.loads(PROPOSAL.read_bytes())
    scan(request)
    direct_checks = list(checks)
    directory_checks = []
    for name in ['proposal_directory', 'production_work_directory']:
        item = absolute(request[name])
        directory_checks.append({'context': name, 'path': str(item), 'exists': item.exists(),
            'status': 'FUTURE_OUTPUT_PATH_AVAILABLE' if not item.exists() else 'ALREADY_EXISTS_CHECK_NEW_FILLED_REQUEST'})
    draft = absolute(request['frozen_draft']['directory'])
    manifest('frozen_draft_manifest', draft / 'files.json', request['frozen_draft']['manifest_sha256'])
    check('frozen_draft_Solution', draft / 'Solution.lean', request['frozen_draft']['solution_sha256'],
          request['frozen_draft']['solution_bytes'])
    plan = json.loads((draft / 'candidate-parameters.json').read_bytes())
    assert plan['solution_sha256'] == request['frozen_draft']['solution_sha256']
    assert plan['solution_bytes'] == request['frozen_draft']['solution_bytes']
    corrections = []
    gates, stage_summaries = [], []
    for index, stage in enumerate(request['ordinary_stages']):
        gate_item = absolute(stage['gate']['path'])
        expected = stage['gate']['sha256']
        if sha(gate_item) != expected:
            candidates = [p for p in gate_item.parent.glob('w9a2-ordinary-*.json') if sha(p) == expected]
            assert len(candidates) == 1, 'No unique same-hash existing gate counterpart'
            corrected = candidates[0]
            corrections.append({'context': 'ordinary_stages[' + str(index) + '].gate.path',
                'frozen_incorrect_path': stage['gate']['path'],
                'unique_matching_path': corrected.relative_to(ROOT).as_posix(),
                'sha256_unchanged': expected, 'proposal_edited': False})
            gate_item = corrected
        check('stages[' + str(index) + '].correct_gate', gate_item, expected)
        gate = json.loads(gate_item.read_bytes()); gates.append(gate)
        scan(gate['source_files'], 'stages[' + str(index) + '].gate.source_files')
        scan(gate['reused_oleans'], 'stages[' + str(index) + '].gate.reused_oleans')
        scan(gate['lean'], 'stages[' + str(index) + '].gate.lean')
        archive_item = absolute(stage['archive_manifest']['path'])
        manifest('stages[' + str(index) + '].archive', archive_item, stage['archive_manifest']['sha256'])
        archive_dir = absolute(stage['archived_job_directory'])
        job = absolute(gate['work_directory'])
        assert archive_dir.is_dir() and job.is_dir()
        for name in ['started.json', 'terminal.json']:
            assert (archive_dir / name).read_bytes() == (job / name).read_bytes()
            pin(job / name)
        started = json.loads((job / 'started.json').read_bytes())
        terminal = json.loads((job / 'terminal.json').read_bytes())
        assert started['gate_sha256'] == expected
        attestation = json.loads(absolute(stage['root_attestation']['path']).read_bytes())
        session = attestation.get('root_observed_parent_session', attestation.get('root_observed_previous_parent_session'))
        assert type(session) is int and session > 0
        assert attestation['actual_parent_exit_code'] == (0 if terminal['passed'] else 1)
        if 'job' in attestation:
            assert absolute(attestation['job']).resolve() == job.resolve()
        stage_summaries.append({'index': index, 'gate_path_used_for_readonly_review': str(gate_item),
            'gate_sha256': expected, 'started_pid': started['pid'], 'root_recorded_session': session,
            'root_recorded_actual_exit_code': attestation['actual_parent_exit_code'],
            'whole_stage_passed': terminal['passed'], 'modules_completed': terminal['modules_completed']})
    final_sources = {row['module']: row['sha256'] for row in plan['source_modules']}
    final_sources['StructuralW9A220261020.Prefix'] = 'bfd774658f3f855596a5453f86f4d98fbc884ca651b3e595d68f70b9553f5b3c'
    assert final_sources['StructuralW9A220261020.Core'] == 'c2af225175f9a5ab14d2ba2612714a21e0613f66107a1d75b9d47bf1c77ba02a'
    final_sources['StructuralW9A220261020.Core'] = '26e23c7fc4fbae33bdfff446901eaeb0f22f0f08fe13fa4e326541565a25279f'
    selected, roots = [], {}
    for choice in request['selected_development_modules']:
        module = choice['module']; index = choice['stage_index']; gate = gates[index]
        target = next(row for row in gate['targets'] if row['module'] == module)
        job = absolute(gate['work_directory']); name = module.replace('.', '_')
        receipt = json.loads((job / (name + '.receipt.json')).read_bytes())
        pin(job / (name + '.receipt.json'))
        assert receipt['ordinary_compile_passed'] is True and type(receipt['exit_code']) is int and receipt['exit_code'] == 0
        assert receipt['source_unchanged'] is True and receipt['source_sha256'] == final_sources[module]
        source = absolute(target['source'])
        check('selected[' + module + '].source', source, final_sources[module])
        check('selected[' + module + '].job_source', job / (name + '.lean'), final_sources[module])
        check('selected[' + module + '].olean', job / 'lib' / Path(*module.split('.')).with_suffix('.olean'), receipt['olean_sha256'])
        log = job / (name + '.log'); check('selected[' + module + '].log', log, receipt['log_sha256'])
        text = log.read_text(encoding='utf-8')
        observed = {n: [x.strip() for x in raw.split(',') if x.strip()] for n, raw in
            re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S)}
        observed.update({n: [] for n in re.findall(r"'([^']+)' does not depend on any axioms", text)})
        assert observed == receipt['observed_axioms'] and set(observed) == set(target['printed_roots'])
        assert all(set(values) <= ALLOWED for values in observed.values())
        assert not set(roots).intersection(observed); roots.update(observed)
        selected.append({'module': module, 'stage_index': index, 'source_sha256': receipt['source_sha256'],
                         'olean_sha256': receipt['olean_sha256'], 'observed_axioms': observed, 'read_only_pin_audit': 'PASS'})
    assert len(roots) == 12
    runtime_v3_script = ROOT / 'research-goal-20261020-w9a2-runtime-closure-v3/assemble.py'
    route_updates = {'scope': 'Latest route pointers only; NOT a current completed-runtime assertion',
        'frozen_setup_runner_v2_hash_pair_matches_but_is_superseded': True,
        'filled_request_must_select_actual_completed_runtime_version': {
            'prospective_v3_setup_runner': pin(runtime_v3_script),
            'prospective_v3_closure_path': 'tmp/w9a2-20261020/trusted-runtime-closure-v3/closure.json',
            'closure_sha256': None, 'actual_setup_parent_exit0_observed_by_this_review': False},
        'logical_setup_outer_role_remains': 'trusted-runtime-closure-v1',
        'fresh_record_and_actual_setup_terminal_must_be_filled_after_observation': True}
    # Rehash every inspected existing file after the scan; runtime live outputs
    # were never read or inspected. Only its frozen v3 source was hashed.
    for entry in pins.values():
        item = Path(entry['path'])
        assert str(item.resolve()) == entry['resolved_path'] and item.stat().st_size == entry['bytes'] and sha(item) == entry['sha256']
    mismatches = [row for row in checks if row['status'] != 'PASS']
    assert len(mismatches) == 1 and len(corrections) == 1
    report = {'schema': 'w9a2-frozen-request-independent-path-review-v1',
        'reviewed_at_utc': datetime.now(timezone.utc).isoformat(),
        'scope': 'Read-only filesystem/path/SHA/receipt/type-identity audit only; no assembler or proof/tool execution',
        'frozen_proposal_sha256_unchanged': PROPOSAL_SHA, 'frozen_package_sha256_unchanged': PREPARED_SHA,
        'direct_request_checks': direct_checks, 'all_expanded_file_pin_checks': checks,
        'direct_nonplaceholder_path_hash_pairs': len([r for r in direct_checks if '.files[' not in r['context']]),
        'only_mismatches': mismatches, 'unique_in_memory_corrections_for_root_NEW_request': corrections,
        'future_output_directories': directory_checks, 'intentionally_unfilled': pending,
        'stage_job_archive_and_root_attestation_bridges': stage_summaries,
        'selected_module_final_source_identity': selected, 'twelve_selected_printed_axiom_roots': roots,
        'runtime_route_updates_separate_from_hash_mismatches': route_updates,
        'all_inspected_inputs_rehashed_unchanged': True, 'inspected_input_count': len(pins),
        'frozen_files_modified': False, 'executor_compiler_export_kernel_network_calls': 0,
        'production_or_setup_pass_claimed': False}
    emit(HERE / 'review.json', report)
    emit(HERE / 'input-pins.json', {'scope': report['scope'], 'files': list(pins.values())})
    print(json.dumps({'expanded_pin_checks': len(checks), 'mismatches': len(mismatches),
        'only_correction': corrections[0], 'inputs_unchanged': len(pins), 'selected_axiom_roots': len(roots),
        'proof_or_executor_calls': 0}))


if __name__ == '__main__':
    main()
