"""Read-only source/hash/AST audit capture; never imports or runs a verifier."""
from pathlib import Path
from datetime import datetime, timezone
import ast
import difflib
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
V0 = ROOT / 'research-goal-20261020-w9a2-verification-preparation'
V1 = ROOT / 'research-goal-20261020-w9a2-verification-preparation-v1'
EXPECTED = {
    V0.name: 'd3fe63a5bfb293d2bd860bb8549575723cf791cec20ad03213e69a7f4f0852ff',
    V1.name: '3dc697cd99c9a38730b4e32cef02fd1f780f74ffeaa1512e6e52500d9e6e3e53',
}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def metadata(path):
    raw = path.read_bytes()
    return {'path': path.relative_to(ROOT).as_posix(), 'bytes': len(raw), 'sha256': sha(raw)}


def main():
    before = []
    versions = []
    for directory in [V0, V1]:
        manifest = directory / 'prepared-files.json'
        assert sha(manifest.read_bytes()) == EXPECTED[directory.name]
        before.append(metadata(manifest))
        rows = json.loads(manifest.read_bytes())['files']
        for row in rows:
            actual = metadata(directory / row['path'])
            assert (actual['bytes'], actual['sha256']) == (row['bytes'], row['sha256'])
            before.append(actual)
        versions.append({'version': directory.name, 'manifest_sha256': EXPECTED[directory.name],
                         'pinned_file_count': len(rows), 'all_manifest_rows_matched': True})
    old = (V0 / 'run_verification.py').read_bytes()
    new = (V1 / 'run_verification.py').read_bytes()
    old_token = b"self.wsl_command('/usr/bin/setsid','/bin/sh'"
    new_token = b"self.wsl_command('/usr/bin/setsid','--wait','/bin/sh'"
    assert old.count(old_token) == 1 and old.replace(old_token, new_token) == new
    diff = ''.join(difflib.unified_diff(old.decode().splitlines(keepends=True),
        new.decode().splitlines(keepends=True), fromfile='v0/run_verification.py',
        tofile='v1/run_verification.py')).encode()
    assert diff == (V1 / 'v0-to-v1-runner.diff').read_bytes()
    with (HERE / 'v0-to-v1-runner.diff').open('xb') as stream:
        stream.write(diff)
    module = ast.parse(new)
    constants = {}
    for node in module.body:
        if isinstance(node, ast.Assign) and isinstance(node.targets[0], ast.Name):
            try:
                constants[node.targets[0].id] = ast.literal_eval(node.value)
            except (ValueError, TypeError):
                pass
    assert constants['BUDGET'] == 3200.0
    assert constants['ALLOWED'] == ['propext', 'Quot.sound', 'Classical.choice']
    expected_roots = ['candidate_strict_improvement', 'candidate_critical_line_bound',
                      'candidate_critical_line_bound_cumulative']
    assert constants['TARGETS'] == expected_roots
    core = ROOT / 'tools/ComparatorCoreAudit.lean'
    assert sha(core.read_bytes()) == constants['CORE_AUDIT_SHA']
    before.append(metadata(core))
    tool_rows = []
    for logical, expected in constants['TOOL_SOURCE_LF_SHA'].items():
        actual = ROOT / 'tmp' / logical
        row = metadata(actual)
        before.append(row)
        canonical = sha(actual.read_bytes().replace(b'\r\n', b'\n'))
        assert canonical == expected
        tool_rows.append({'logical_name': logical, 'canonical_LF_sha256': canonical})
    for relative in ['tmp/nanoda/src/main.rs', 'tmp/nanoda/src/tc.rs', 'tmp/nanoda/src/util.rs',
                     'scripts/verify_single_solution.py',
                     'research-goal-20261020-w9a2-delivery/draft-v0/files.json',
                     'StructuralW9A220261020/Core.lean']:
        before.append(metadata(ROOT / relative))
    for filename in ['gate-template.json', 'runtime-closure-template.json', 'static-audit.json']:
        json.loads((V1 / filename).read_bytes())
    gate = json.loads((V1 / 'gate-template.json').read_bytes())
    closure = json.loads((V1 / 'runtime-closure-template.json').read_bytes())
    assert gate['allow_verification_execution'] is False
    assert gate['runtime']['root_reviewed_complete_runtime_closure'] is False
    assert closure['complete_source_bound_runtime_closure_verified'] is False
    after = [metadata(ROOT / row['path']) for row in before]
    assert before == after
    output = {
        'schema': 'w9a2-verification-independent-static-v1',
        'status': 'PASS_STATIC_AFTER_VERSIONED_FIX_NOT_EXECUTED',
        'captured_at_utc': datetime.now(timezone.utc).isoformat(),
        'scope': 'Read-only source, JSON, AST, finite source-diff and before/after byte hashes; no verifier module imported, no compiler/exporter/Comparator/kernel/nanoda run.',
        'versions': versions,
        'runner_v0_sha256': sha(old), 'runner_v1_sha256': sha(new),
        'only_runner_change': 'Insert --wait immediately after /usr/bin/setsid in the Windows nanoda argv.',
        'independently_recreated_diff_equals_delivery_diff': True,
        'diff_sha256': sha(diff),
        'original_CoreAudit_sha256': constants['CORE_AUDIT_SHA'],
        'eight_pinned_tool_sources': tool_rows,
        'budget_seconds_literal': constants['BUDGET'],
        'public_roots_literal': expected_roots,
        'allowed_axioms_literal': constants['ALLOWED'],
        'gate_template_execution_enabled': False,
        'runtime_closure_template_verified': False,
        'input_before': before, 'input_after': after, 'input_bytes_unchanged': True,
        'reviewer_executions': {'runner': 0, 'compiler': 0, 'exporter': 0,
                                'Comparator': 0, 'default_Lean_replay': 0, 'nanoda': 0},
        'candidate_source_mutations': 0,
        'main_round_counter_changed': False,
        'runtime_Dll_Elf_closure_actually_audited': False,
        'ordinary_or_fullchain_success_claimed': False,
        'website_or_GitHub_acceptance_claimed': False,
        'setsid_primary_source': 'https://raw.githubusercontent.com/util-linux/util-linux/master/sys-utils/setsid.c',
        'setsid_source_scope': 'Lines 92-107: when setsid forks, --wait is needed to propagate the child exit status. This audit does not attest the actual installed WSL utility build.'
    }
    with (HERE / 'review.json').open('x', encoding='utf-8', newline='\n') as stream:
        json.dump(output, stream, ensure_ascii=False, indent=2)
        stream.write('\n')
    print(json.dumps({'status': output['status'], 'input_rows_checked': len(before),
                      'v1_runner_sha256': sha(new), 'review_sha256': sha((HERE / 'review.json').read_bytes())}))


if __name__ == '__main__':
    main()
