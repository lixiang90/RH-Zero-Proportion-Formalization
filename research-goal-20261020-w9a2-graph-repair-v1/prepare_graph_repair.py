"""Freeze one proof-line repair using text/hash operations only; no Lean main."""
from datetime import datetime, timezone
import difflib
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
REL = 'StructuralW9A220261020/Graph.lean'
OLD = b'  all_goals norm_num [gsum_range, natGaps, reverse8, Finset.sum_range_succ] <;> ring\r\n'
NEW = b'  all_goals norm_num [gsum_range, natGaps, reverse8, Finset.sum_range_succ] <;> simp only [Fin.reduceFinMk] <;> ring\r\n'
TERMINAL = ROOT / 'research-goal-20261020-w9a2-ordinary-v1-terminal'
OBSERVED = {}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read(path):
    raw = path.read_bytes()
    key = path.resolve().relative_to(ROOT.resolve()).as_posix()
    val = {'path': key, 'bytes': len(raw), 'sha256': sha(raw)}
    assert OBSERVED.setdefault(key, val) == val, key
    return raw


def row(path, base):
    raw = path.read_bytes()
    return {'path': path.relative_to(base).as_posix(), 'bytes': len(raw), 'sha256': sha(raw)}


def write(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as stream:
        stream.write(raw)


def dump(obj):
    return (json.dumps(obj, ensure_ascii=False, indent=2) + '\n').encode()


def main():
    original = read(ROOT / REL)
    assert len(original) == 17334 and sha(original) == 'a2e4f4fcc8068a245aafaff56363060ffcf4e06e1fccb63d57a999cfb68f0783'
    assert original.count(OLD) == 1 and NEW not in original
    repaired = original.replace(OLD, NEW)
    assert repaired.replace(NEW, OLD) == original and repaired.count(NEW) == 1
    lines0, lines1 = original.splitlines(keepends=True), repaired.splitlines(keepends=True)
    changes = [(i + 1, a, b) for i, (a, b) in enumerate(zip(lines0, lines1)) if a != b]
    assert len(lines0) == len(lines1) and changes == [(151, OLD, NEW)]
    st0 = re.findall(rb'(?ms)^theorem reverse_span (.*?) := by\r?\n', original)
    st1 = re.findall(rb'(?ms)^theorem reverse_span (.*?) := by\r?\n', repaired)
    assert len(st0) == len(st1) == 1 and st0 == st1
    # The complete line projection entails byte identity of every definition,
    # finite packet, other proof, public statement, cost, threshold and API.
    for name in ['Core', 'Localization', 'Counting', 'Final']:
        read(ROOT / ('StructuralW9A220261020/' + name + '.lean'))
    core = ROOT / 'research-goal-20261020-w9a2-core-repair-v1/development-split/StructuralW9A220261020/Core.lean'
    assert sha(read(core)) == '26e23c7fc4fbae33bdfff446901eaeb0f22f0f08fe13fa4e326541565a25279f'
    terminal_manifest = read(TERMINAL / 'files.json')
    assert sha(terminal_manifest) == '272ddcae631c5380a46581e409300dbc0d27ad68f2562a951896ea6fd16660cc'
    terminal = json.loads(terminal_manifest)
    assert terminal['root_observed_parent_session'] == 93720 and terminal['actual_parent_exit_code'] == 1
    copies = [('files.json', terminal_manifest)]
    for item in terminal['files']:
        target = (TERMINAL / item['path']).resolve()
        assert target.is_relative_to(TERMINAL.resolve())
        raw = read(target)
        assert len(raw) == item['bytes'] and sha(raw) == item['sha256']
        copies.append((item['path'], raw))
    failure = json.loads(read(TERMINAL / 'StructuralW9A220261020_Graph.receipt.json'))
    success = json.loads(read(TERMINAL / 'StructuralW9A220261020_Core.receipt.json'))
    start = json.loads(read(TERMINAL / 'started.json'))
    log = read(TERMINAL / 'StructuralW9A220261020_Graph.log')
    assert failure['exit_code'] == 1 and failure['elapsed_seconds'] == 64.25
    assert failure['log_sha256'] == sha(log) == '84d5043523b3c7a534bcddc40e0f1af34c54e934b2c2cb4ef046d68345c6353f'
    errors = re.findall(rb'(?m)^.*:[0-9]+:[0-9]+: error:.*$', log)
    assert len(errors) == 1 and b'Graph.lean:148:70: error: unsolved goals' in errors[0]
    assert success['exit_code'] == 0 and success['ordinary_compile_passed'] is True
    assert success['source_sha256'] == sha(read(core))
    assert success['olean_sha256'] == '4e24ca2145281fb866d4b24f4db11da74aa87cb4728796fc856e5e4f0ab3fc07'
    assert start['gate_sha256'] == '92def59e80c77b461e3cc301bff748f65e44d53b4c031d745098b156882a3bc5'
    rules = []
    for path, first, last in [
        ('tmp/lean-toolchain/src/lean/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Fin.lean', 102, 110),
        ('.lake/packages/mathlib/Mathlib/Tactic/NormNum/Core.lean', 215, 249),
        ('.lake/packages/mathlib/Mathlib/CategoryTheory/ComposableArrows/Basic.lean', 47, 59),
        ('.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/AddSubMap.lean', 85, 89),
    ]:
        raw = read(ROOT / path)
        rules.append({'path': path, 'bytes': len(raw), 'sha256': sha(raw), 'first_line': first,
                      'last_line': last, 'exact_excerpt': ''.join(raw.decode().splitlines(keepends=True)[first-1:last])})
    before = list(OBSERVED.values())
    for item in before:
        read(ROOT / item['path'])
    report = {
        'status': 'PREPARED_PROOF_ONLY_REPAIR_NOT_COMPILED',
        'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
        'failure': {'gate_sha256': start['gate_sha256'], 'parent_session': 93720,
            'root_observed_parent_exit_code': 1, 'module': failure['module'],
            'exit_code': failure['exit_code'], 'elapsed_seconds': failure['elapsed_seconds'],
            'log_sha256': sha(log), 'sole_error': errors[0].decode(),
            'diagnostic': 'Reflected Fin.mk literal indices remain syntactically distinct from finite numerals when ring atomizes g applications.'},
        'change': {'theorem': 'StructuralW9A220261020.Graph.reverse_span', 'source_line': 151,
            'old_line': OLD.decode().rstrip('\r\n'), 'new_line': NEW.decode().rstrip('\r\n'),
            'byte_delta': len(repaired) - len(original),
            'scope': 'Insert a separate simp only [Fin.reduceFinMk] after the unchanged norm_num and before the unchanged ring.'},
        'reason_separate_simp_required': 'NormNum.getSimpContext retains ctx but discards elabSimpArgs simprocs; its methods invoke preDefault/postDefault with empty simproc arrays. A separate simp invocation runs the existing builtin Fin reduction explicitly.',
        'original_source': {'bytes': len(original), 'sha256': sha(original)},
        'repaired_source': {'path': REL, 'bytes': len(repaired), 'sha256': sha(repaired)},
        'forward_projection_exact': True, 'reverse_projection_exact': True,
        'theorem_statement_unchanged': True, 'theorem_statement_sha256': sha(st0[0]),
        'all_bytes_outside_single_proof_line_unchanged': True,
        'definitions_literals_134_edges_2267_exclusions_StateAt_roots_costs_threshold_changes': 0,
        'previous_Core_ordinary_pass': success,
        'source_inputs_before': before, 'source_inputs_after': list(OBSERVED.values()),
        'original_inputs_unchanged': True, 'compiler_export_kernel_search_runs': 0,
        'main_round_counter_changed': False, 'ordinary_pass_claimed_for_repaired_Graph': False,
        'Comparator_passed': False, 'independent_kernel_passed': False,
        'website_submission_ready': False, 'requires_new_root_frozen_gate_before_compile': True}
    write(HERE / REL, repaired)
    write(HERE / 'Graph-v0.lean', original)
    delta = ''.join(difflib.unified_diff(original.decode().splitlines(keepends=True),
        repaired.decode().splitlines(keepends=True), fromfile='canonical-v0/' + REL,
        tofile='graph-repair-v1/' + REL))
    write(HERE / 'Graph-v0-to-v1.diff', delta.encode())
    write(HERE / 'repair.json', dump(report))
    write(HERE / 'proof-rule-evidence.json', dump({'scope': 'Static source evidence only; no proof execution', 'sources': rules}))
    for name, raw in copies:
        write(HERE / 'failed-ordinary-v1-evidence' / name, raw)
    print(json.dumps({'source_sha256': sha(repaired), 'source_bytes': len(repaired),
                      'delta_bytes': len(repaired)-len(original), 'repair_json_sha256': sha(dump(report)),
                      'proof_execution_count': 0}))


if __name__ == '__main__':
    main()
