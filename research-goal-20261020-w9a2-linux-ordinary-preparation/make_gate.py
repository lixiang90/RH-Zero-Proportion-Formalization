"""Prepare a runtime-bound proposal after setup; never authorize or run Lean.

Run only after actual runtime-v0/runtime.json exists. Root reviews the proposal,
then writes a new authorized gate with its exact hash. A failed trusted import
does not permit this helper to create a candidate proposal.
"""
from pathlib import Path
import argparse
import hashlib
import json

REPO = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
RUNTIME = Path('/var/tmp/rh-zero-w9a2-20261020/runtime-v0/runtime.json')
VERSION = 'Lean (version 4.33.0-rc2, x86_64-unknown-linux-gnu, commit d8b18978322de05a8f3dba51ef03cf5461676c17, Release)'
ORIGINAL_PROPOSAL = REPO / 'research-goal-20261020-w9a2-formal-static-review/candidate-ordinary-gate-proposal.json'
ORIGINAL_PROPOSAL_SHA = '4486a57c7a4cbd2e4f4f305c32c692c9c4e8aabf8f8c07a6da567aa7e17a7d37'


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as source:
        for block in iter(lambda: source.read(1048576), b''):
            h.update(block)
    return h.hexdigest()


def row(path):
    path = Path(path).resolve()
    assert path.is_relative_to(REPO)
    return {'path': path.relative_to(REPO).as_posix(), 'sha256': sha(path)}


def create(path, value):
    path = (REPO / path).resolve()
    assert path.is_relative_to(REPO)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x', encoding='utf-8') as out:
        json.dump(value, out, indent=2)
        out.write('\n')
    print(json.dumps({'proposal': path.relative_to(REPO).as_posix(), 'sha256': sha(path),
                      'authorized': False, 'compiler_invocations': 0}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('stage', choices=['trusted', 'candidate'])
    parser.add_argument('--windows-terminal-evidence', required=True)
    parser.add_argument('--output', required=True)
    parser.add_argument('--trusted-metadata', default='tmp/w9a2-20261020/linux-trusted-v0')
    args = parser.parse_args()
    assert sha(ORIGINAL_PROPOSAL) == ORIGINAL_PROPOSAL_SHA
    original = json.loads(ORIGINAL_PROPOSAL.read_text(encoding='utf-8'))
    runtime = json.loads(RUNTIME.read_text())
    assert runtime['status'] == 'SETUP_ONLY_PORTABILITY_UNTESTED'
    assert sha(runtime['lean']) == runtime['lean_sha256'] == 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
    assert runtime['compiler_archive_sha256'] == '48010c7d6264dc992574e9b0e09ece1f9c648e8f5106066b2cdb6834a6a60a6c'
    assert sha(runtime['mirror_manifest']) == runtime['mirror_manifest_sha256']
    terminal_evidence = (REPO / args.windows_terminal_evidence).resolve()
    evidence = json.loads(terminal_evidence.read_text(encoding='utf-8'))
    assert evidence['windows_compiler_terminal_confirmed'] is True
    assert evidence['observed_windows_lean_processes'] == []
    required = ['original_exec_session_id', 'original_parent_pid', 'original_lean_pid', 'observed_at_UTC']
    assert all(key in evidence for key in required)
    gate = {
        'authorized': False, 'proposal_only': True, 'task': 'w9a2-linux-ordinary-source-pinned',
        'stage': args.stage, 'automatic_repairs_or_retries': 0, 'max_parallel_compilers': 1,
        'runner_sha256': sha(HERE / 'run.py'), 'runtime_manifest': str(RUNTIME),
        'runtime_manifest_sha256': sha(RUNTIME),
        'runtime_mirror_manifest_sha256': runtime['mirror_manifest_sha256'],
        'compiler_archive_sha256': runtime['compiler_archive_sha256'],
        'lean': {'path': runtime['lean'], 'sha256': runtime['lean_sha256'], 'version': VERSION},
        'package_commits': {e['name']: e['commit'] for e in runtime['package_source_pins']},
        'root_confirmed_original_windows_handle_terminal': True,
        'windows_terminal_evidence': row(terminal_evidence),
        'hard_seconds_per_target': 7200, 'hard_seconds_per_batch': 28800,
        'stop': 'First failed import/compile/pin/axiom/timeout stops; retain source/log/handle; zero automatic retry or dependency rebuild.',
        'runtime_scope': 'Linux modular ordinary development only; no single-file, Comparator, independent-kernel or production-time acceptance.',
        'source_files': [row(HERE / f) for f in ['run.py', 'make_gate.py', 'trusted-source/ChallengeDeps.lean', 'trusted-audit-generation.json']],
        'reused_oleans': [],
        'pending_before_root_authorization': ['Root inspects actual original Windows terminal evidence and fresh Linux/Windows no-Lean observation.',
            'Root reviews runtime/mirror/source pins and this exact stage; writes a NEW authorized gate and computes its exact SHA.'],
    }
    if args.stage == 'trusted':
        gate.update(work_directory='/var/tmp/rh-zero-w9a2-20261020/dev/trusted-v0',
                    metadata_mirror='tmp/w9a2-20261020/linux-trusted-v0')
        gate['source_files'] += [row(REPO / 'research-goal-20261020-w9a2-linux-setup/TrustedImport.lean'),
            row(REPO / 'research-goal-20261020-w9a2-runtime/trusted/ChallengeDeps.lean')]
        gate['targets'] = [
            {'module': 'TrustedImport', 'source': 'research-goal-20261020-w9a2-linux-setup/TrustedImport.lean', 'printed_roots': []},
            {'module': 'ChallengeDeps', 'source': 'research-goal-20261020-w9a2-linux-ordinary-preparation/trusted-source/ChallengeDeps.lean',
             'printed_roots': ['Ncount', 'N0star', 'cMT']},
        ]
    else:
        prior = (REPO / args.trusted_metadata).resolve()
        terminal = json.loads((prior / 'terminal.json').read_text())
        probe = json.loads((prior / 'TrustedImport.receipt.json').read_text())
        receipt = json.loads((prior / 'ChallengeDeps.receipt.json').read_text())
        assert terminal['passed'] and terminal['stage'] == 'trusted' and terminal['modules_completed'] == 2
        assert probe['ordinary_compile_passed'] and probe['exit_code'] == 0
        assert receipt['ordinary_compile_passed'] and receipt['axiom_audit_passed'] and receipt['exit_code'] == 0
        assert receipt['source_unchanged'] and receipt['source_sha256'] == sha(HERE / 'trusted-source/ChallengeDeps.lean')
        assert sha(receipt['olean_path']) == receipt['olean_sha256']
        gate.update(work_directory='/var/tmp/rh-zero-w9a2-20261020/dev/ordinary-v0',
                    metadata_mirror='tmp/w9a2-20261020/linux-ordinary-v0',
                    trusted_terminal=row(prior / 'terminal.json'),
                    trusted_module_receipt=row(prior / 'ChallengeDeps.receipt.json'),
                    trusted_source_sha256=receipt['source_sha256'])
        gate['source_files'] += original['source_files'] + [row(ORIGINAL_PROPOSAL),
            row(prior / 'terminal.json'), row(prior / 'TrustedImport.receipt.json'), row(prior / 'ChallengeDeps.receipt.json')]
        gate['targets'] = original['targets']
        gate['reused_oleans'] = [{'path': receipt['olean_path'], 'module_path': 'ChallengeDeps.olean',
                                  'sha256': receipt['olean_sha256']}]
    # Deduplicate only identical pins; never select between differing versions.
    unique = {}
    for entry in gate['source_files']:
        assert entry['path'] not in unique or unique[entry['path']] == entry
        assert sha(REPO / entry['path']) == entry['sha256']
        unique[entry['path']] = entry
    gate['source_files'] = list(unique.values())
    create(args.output, gate)


if __name__ == '__main__':
    main()
