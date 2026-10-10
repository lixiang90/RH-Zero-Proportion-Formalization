"""Verify additive ninth-span publication bindings; never delete old records.

Use --check-index after staging to verify the bytes actually committed.  Without
that option, the check binds the current working tree and the two proof receipts.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BASE = '5ec0472d125a61f9433920ebd4d29e72486b126e'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
HEADLINES = {'RHWeilRecord.NinthSpan.' + name for name in
             ('local_certificate', 'simple_dyadic', 'simple_cumulative',
              'distinct_dyadic', 'distinct_cumulative', 'previous_recordRatio_lt')}
PINS = {
    'scripts/am_ninth_span_certificate.py': 'b03b3259a385702300520bd02f33c79d228b76a0e07c6b42cec23b6a02a5e673',
    'output/am-ninth-span-certificate.json': '9fc7f9d8a00ebbc3e2f8ff236b247af5ac3173c3942ec72b9180c4473a65cf96',
    'output/am-ninth-span-point-catalog.json': 'cda8ce5fce3d0a639975f54e57b1991c7d5a2a2cb112df4e3dd13237a954fb27',
    'submission/proof/Solution.lean': 'd52f013f7edcc8536a28ef3908e64a967e5b9184d6546952cb5a541dc6d65e8a',
    'papers/ninth-span-simple-critical-paper.tex': 'f2f2ab09623b0fab9251e15a0d9d445d380a67b66aa32b30f70d4581d23ed71d',
    'output/pdf/ninth-span-simple-critical-paper.pdf': '6e4dcc129820c24d53ae2ac0d976a48bf4379dbf0c7fbdb7b40a9c9a45ca9382',
}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args: str) -> list[str]:
    return ['git', '--git-dir', str(ROOT/'.git'), '--work-tree', str(ROOT), *args]


class GitBlobs:
    """Stream blob hashes with one Git process instead of hundreds of launches."""
    def __enter__(self):
        self.proc = subprocess.Popen(git('cat-file', '--batch'), stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        return self

    def digest(self, reference: str) -> str:
        assert '\n' not in reference and '\r' not in reference
        self.proc.stdin.write(reference.encode('utf8') + b'\n')
        self.proc.stdin.flush()
        header = self.proc.stdout.readline().rstrip(b'\n').rsplit(b' ', 2)
        assert len(header) == 3 and header[1] == b'blob', f'Missing Git blob: {reference}'
        remaining = int(header[2])
        result = hashlib.sha256()
        while remaining:
            block = self.proc.stdout.read(min(remaining, 1024*1024))
            assert block, f'Truncated Git blob: {reference}'
            result.update(block)
            remaining -= len(block)
        assert self.proc.stdout.read(1) == b'\n', f'Invalid Git batch framing: {reference}'
        return result.hexdigest()

    def __exit__(self, exc_type, exc, traceback):
        self.proc.stdin.close()
        if exc_type is not None:
            self.proc.terminate()
        code = self.proc.wait(timeout=30)
        error = self.proc.stderr.read().decode('utf8', errors='replace')
        self.proc.stdout.close()
        self.proc.stderr.close()
        if exc_type is None:
            assert code == 0, error


def verify(check_index: bool, output: Path | None) -> dict:
    bindings: dict[str, str] = {}
    def bind(name: str, expected: str | None = None) -> str:
        name = name.replace('\\', '/')
        path = ROOT/name
        assert path.resolve().is_relative_to(ROOT.resolve()), f'Input is outside repository: {name}'
        assert output is None or path.resolve() != output, f'Output would overwrite an input: {name}'
        assert path.is_file(), f'Missing publication input: {name}'
        actual = sha(path)
        if expected is not None:
            assert actual == expected, f'Publication input hash mismatch: {name}'
        if name in bindings:
            assert bindings[name] == actual, f'Input changed during check: {name}'
        bindings[name] = actual
        return actual

    baseline_name = 'verification/ninth-span-old-record-baseline.json'
    bind(baseline_name)
    baseline = json.loads((ROOT/baseline_name).read_text(encoding='utf8'))
    assert baseline['base_commit'] == BASE
    assert baseline['tracked_count'] == len(baseline['files']) == 658
    retained = 0
    for name, old in baseline['files'].items():
        assert (ROOT/name).is_file(), f'Old tracked file disappeared: {name}'
        if name == '.gitattributes':
            continue
        actual_name = 'docs/c260-repository-status-20261010.md' if name == 'README.md' else name
        assert (ROOT/actual_name).stat().st_size == old['bytes'], f'Old file size changed: {name}'
        assert sha(ROOT/actual_name) == old['raw_sha256'], f'Old file bytes changed: {name}'
        retained += 1
    for name, pin in PINS.items():
        bind(name, pin)
    deletions = subprocess.check_output(git('diff', '--name-only', '--diff-filter=D', BASE)).decode('utf8').strip()
    assert not deletions, f'Old tracked deletions: {deletions}'

    finite_name = 'verification/ninth-span-exact-certificate.json'
    bind(finite_name)
    finite = json.loads((ROOT/finite_name).read_text(encoding='utf8'))
    assert finite['finite_certificate_pass'] is True
    assert finite['domains'] == 2399 and finite['closed_branches'] == 84
    assert finite['uniform_reward'] == '805403/100000000'
    assert finite['simple_critical_proportion'] == '941021/1397107'
    assert finite['certificate_raw_sha256'] == PINS['output/am-ninth-span-certificate.json']
    assert finite['checker_raw_sha256'] == PINS['scripts/am_ninth_span_certificate.py']

    formal_name = 'verification/ninth-span-complete-formal-kernel.json'
    formal_hash = bind(formal_name)
    formal = json.loads((ROOT/formal_name).read_text(encoding='utf8'))
    assert formal['module_check_passed'] is True
    assert formal['source_unchanged_during_check'] is True
    assert HEADLINES <= set(formal['observed_axioms']), 'Incomplete ordinary-kernel headline audit'
    assert formal['audit_exit_code'] == 0
    assert all(set(a) <= ALLOWED for a in formal['observed_axioms'].values())
    assert set(formal['source_sha256']) == set(formal['olean_sha256']), 'Missing formal source/olean binding'
    assert 'RecordProportion.NinthSpan' in formal['source_sha256']
    bind('scripts/verify_ninth_span_kernel.py', formal['driver_sha256'])
    assert formal['reused_olean_unchanged'] is True
    assert formal['reused_olean_before'] == formal['reused_olean_after']
    steps = formal['build_steps']
    assert {step['module'] for step in steps} == set(formal['modules'])
    assert len(steps) == len(formal['modules'])
    assert set(formal['reused_olean_before']) == set(formal['olean_sha256']) - set(formal['modules'])
    for module, value in formal['reused_olean_before'].items():
        assert value == formal['olean_sha256'][module], f'Reused formal artifact changed: {module}'
    for step in steps:
        assert step['exit_code'] == 0
        assert step['source_sha256'] == formal['source_sha256'][step['module']]
        assert step['output_olean_sha256'] == formal['olean_sha256'][step['module']]
        bind(step['log'], step['log_sha256'])
    bind(formal['audit_log'], formal['audit_log_sha256'])
    for receipt_name, receipt_hash in formal['component_receipts'].items():
        bind(receipt_name, receipt_hash)
        component = json.loads((ROOT/receipt_name).read_text(encoding='utf8'))
        for field in ('published_logs', 'artifacts'):
            entries = component.get(field, {})
            if isinstance(entries, list):
                for entry in entries:
                    bind(entry['path'], entry['sha256'])
            else:
                assert isinstance(entries, dict), f'Invalid component artifact inventory: {receipt_name}'
                for artifact_name, value in entries.items():
                    if isinstance(value, dict):
                        bind(value.get('path', artifact_name), value['sha256'])
                    else:
                        assert isinstance(value, str), f'Invalid component artifact hash: {artifact_name}'
                        bind(artifact_name, value)

    replay_name = 'verification/ninth-span-complete-independent-nanoda.json'
    bind(replay_name)
    replay = json.loads((ROOT/replay_name).read_text(encoding='utf8'))
    assert replay['nano_check_passed'] is True and replay['inputs_unchanged'] is True
    assert replay['actual_nano_exit_code'] == 0 and replay['checked_declarations'] > 0
    assert HEADLINES <= set(replay['roots']), 'Incomplete independent headline replay'
    assert set(replay['observed_axioms']) <= ALLOWED
    assert replay['formal_receipt_sha256'] == formal_hash, 'Independent replay used another formal receipt'
    before, after = replay['sha256_before'], replay['sha256_after']
    assert before == after, 'Independent replay input hashes changed'
    assert before['formal_receipt'] == after['formal_receipt'] == formal_hash
    for module, source_hash in formal['source_sha256'].items():
        name = '/'.join(module.split('.')) + '.lean'
        bind(name, source_hash)
        assert before['source:'+module] == after['source:'+module] == source_hash, f'Stale replay source: {module}'
        olean_hash = formal['olean_sha256'][module]
        art = ROOT/'.lake/build/lib/lean'/Path(*module.split('.')).with_suffix('.olean')
        assert sha(art) == before['olean:'+module] == after['olean:'+module] == olean_hash, f'Stale replay olean: {module}'
    assert before['source_lean'] == after['source_lean'] == formal['source_sha256']['RecordProportion.NinthSpan']
    assert before['source_olean'] == after['source_olean'] == formal['olean_sha256']['RecordProportion.NinthSpan']
    bind('scripts/verify_ninth_span_nanoda.py', before['driver_source'])
    for tool in replay['fresh_exporter_compilation']:
        assert tool['exit_code'] == 0
        key = 'exporter_olean:' + tool['name']
        art = ROOT/'tmp/verification/ninth-span-complete-independent-nanoda/tool-lib'/Path(*tool['name'].split('.')).with_suffix('.olean')
        assert sha(art) == before[key] == after[key] == tool['olean_sha256']
    assert {tool['name'] for tool in replay['fresh_exporter_compilation']} == {'Export', 'Export.Parse'}
    assert replay['export_process_ran'] is True and replay['export_exit_code'] == 0
    public_logs = {name.replace('\\', '/'): value for name, value in replay['published_logs'].items()}
    public_dir = 'verification/ninth-span-complete-independent-nanoda/'
    expected_logs = {public_dir + name for name in
                     ('export.txt', 'nanoda.txt', 'nanoda-time.txt', 'nanoda-config.json', 'exporter-Export.txt', 'exporter-Export.Parse.txt')}
    assert expected_logs <= set(public_logs), 'Missing published independent-check logs'
    for name, value in public_logs.items():
        bind(name, value)
    assert public_logs[public_dir+'nanoda.txt'] == replay['log_sha256']
    assert public_logs[public_dir+'nanoda-config.json'] == before['configuration']
    config = json.loads((ROOT/(public_dir+'nanoda-config.json')).read_text(encoding='utf8'))
    assert config == replay['configuration']
    assert config['use_stdin'] is True and config['unpermitted_axiom_hard_error'] is True
    assert config['unsafe_permit_all_axioms'] is False
    assert config['nat_extension'] is True and config['string_extension'] is True
    assert set(config['permitted_axioms']) == ALLOWED
    assert config['print_success_message'] is True and config['print_axioms'] is True and config['pp_to_stdout'] is True

    # Bind all new public proof support, receipts, scripts, and preserved snapshot
    # files.  Runtime .lake artifacts, ignored .log files, and this check's own
    # output are not publication inputs and cannot be recursively self-hashed.
    candidates = [ROOT/'README.md', ROOT/'.gitattributes',
                  ROOT/'docs/c260-repository-status-20261010.md',
                  ROOT/'docs/ninth-span-formalization.md',
                  ROOT/'papers/ninth-span-simple-critical-paper.tex',
                  ROOT/'papers/ninth-span-lean-verification-addendum.md',
                  ROOT/'output/pdf/ninth-span-simple-critical-paper.pdf']
    candidates += list((ROOT/'scripts').glob('*ninth_span*.py'))
    candidates += list((ROOT/'RecordProportion').glob('NinthSpan*.lean'))
    for path in (ROOT/'verification').glob('ninth-span-*'):
        if path.is_file():
            candidates.append(path)
        elif path.is_dir():
            candidates += [p for p in path.rglob('*') if p.is_file()]
    for path in candidates:
        if path.suffix in {'.log', '.olean', '.ilean'} or (output is not None and path.resolve() == output):
            continue
        bind(path.relative_to(ROOT).as_posix())

    staged_old = 0
    if check_index:
        with GitBlobs() as blobs:
            for name in baseline['files']:
                if name == '.gitattributes':
                    continue
                staged_name = 'docs/c260-repository-status-20261010.md' if name == 'README.md' else name
                assert blobs.digest(':'+staged_name) == blobs.digest(BASE+':'+name), f'Old staged blob changed: {name}'
                staged_old += 1
            for name, expected in sorted(bindings.items()):
                assert blobs.digest(':'+name) == expected, f'Staged bytes differ from checked input: {name}'
    assert all(sha(ROOT/name) == expected for name, expected in bindings.items()), 'Publication inputs changed during check'
    return {'publication_bindings_pass': True, 'old_files_retained': 658,
            'old_file_bytes_checked': retained, 'old_readme_archived_verbatim': True,
            'old_submission_preserved': True, 'formal_receipt_sha256': formal_hash,
            'independent_receipt_sha256': bindings[replay_name],
            'component_receipt_bindings': len(formal['component_receipts']),
            'formal_replay_source_olean_bindings': len(formal['source_sha256']),
            'index_checked': check_index, 'old_base_blobs_checked_in_index': staged_old,
            'staged_input_blobs_checked': len(bindings) if check_index else 0,
            'publication_input_sha256': bindings,
            'output_excluded_from_input_hashes': str(output) if output is not None else None,
            'new_ratio': '941021/1397107', 'independent_declarations': replay['checked_declarations'],
            'submitted_to_website': False}


def main() -> None:
    if not __debug__:
        raise SystemExit('Assertions must remain enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-index', action='store_true', help='Also verify staged Git blobs after git add')
    parser.add_argument('--output', type=Path, help='Save the resulting JSON; relative paths are relative to the repository')
    args = parser.parse_args()
    output = args.output
    if output is not None:
        output = (ROOT/output).resolve() if not output.is_absolute() else output.resolve()
        assert output.suffix == '.json', 'Output must be a JSON receipt'
        assert output != Path(__file__).resolve()
        assert output.name not in {'ninth-span-old-record-baseline.json', 'ninth-span-exact-certificate.json',
            'ninth-span-complete-formal-kernel.json', 'ninth-span-complete-independent-nanoda.json'}, 'Do not overwrite input receipts'
        if output.exists() and output.is_relative_to(ROOT.resolve()):
            previous = json.loads(output.read_text(encoding='utf8'))
            assert isinstance(previous, dict) and 'publication_bindings_pass' in previous, 'Do not overwrite another repository artifact'
    try:
        record = verify(args.check_index, output)
    except Exception as error:
        record = {'publication_bindings_pass': False, 'index_checked': args.check_index,
                  'error': str(error), 'error_type': type(error).__name__}
        if output is not None:
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(json.dumps(record, indent=2)+'\n', encoding='utf8', newline='\n')
        print(json.dumps(record, indent=2))
        raise
    if output is not None:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(record, indent=2)+'\n', encoding='utf8', newline='\n')
    print(json.dumps(record, indent=2))


if __name__ == '__main__':
    main()
