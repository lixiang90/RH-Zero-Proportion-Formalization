"""Byte-only freeze of the terminated, root-gated StrongQuantized v1 run."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
JOB = ROOT / 'tmp/current-s1r-O-20261018/phaseO1'


def item(p):
    b = p.read_bytes()
    return {'path': p.relative_to(ROOT).as_posix(), 'bytes': len(b),
            'sha256': hashlib.sha256(b).hexdigest()}


def main():
    assert json.loads((JOB / 'terminal.json').read_text())['passed'] is True
    source = ROOT / 'StructuralS1RO20261018/PhaseO1/StrongQuantized.lean'
    assert source.read_bytes() == (JOB / 'StrongQuantized.lean').read_bytes()
    receipt = json.loads((JOB / 'StrongQuantized.receipt.json').read_text())
    assert receipt['exit_code'] == 0 and receipt['ordinary_compile_passed']
    assert receipt['axiom_audit_passed'] and receipt['source_unchanged']
    roots = receipt['printed_roots']
    assert len(roots) == 4 and len({r['root'] for r in roots}) == 4
    assert all(set(r['axioms']) == {'propext', 'Classical.choice', 'Quot.sound'} for r in roots)
    assert item(source)['sha256'] == receipt['source_sha256']
    olean = JOB / 'lib/StructuralS1RO20261018/PhaseO1/StrongQuantized.olean'
    assert item(olean)['sha256'] == receipt['olean_sha256']
    prepared = HERE / 'phaseO1-prepared.json'
    prep = json.loads(prepared.read_text())
    for row in prep['files'] + prep['dependencies']:
        assert item(ROOT / row['path'])['sha256'] == row['sha256'], row['path']
    reused = []
    for row in prep['reused_oleans']:
        copied = JOB / 'lib' / row['relative_module_path']
        assert item(copied)['sha256'] == row['sha256']
        reused.append(item(copied))
    out = HERE / 'phaseO1-execution-files.json'
    result = {
        'schema': 'O-actual-strong-v1-execution-v1',
        'actual_exec_session': 13469, 'exec_terminal_exit': 0,
        'files': [item(p) for p in sorted(JOB.iterdir()) if p.is_file()] + [item(Path(__file__))],
        'dependencies': [item(p) for p in [source, prepared,
            HERE / 'execution-v0-files.json',
            ROOT / 'research-goal-20261016/gates/stageO-actual-strong-v1-20261018.json']],
        'compiled_olean_metadata_only': item(olean),
        'reused_oleans_metadata_only': reused,
        'passed_module': receipt,
        'max_RSS_KiB': 6849976,
        'prefix_or_QuantizedComponent_or_CellAQuantitative_recompiled': False,
        'automatic_repairs_or_retries': 0,
        'finite_data_or_Sparse_or_B2_runs': 0,
        'fixed_pair_actual_floor_proved': False,
        'global_floor_proved': False,
        'Nano_replayed': False,
        'scope': 'Four conditional analytic roots for the actual current s1R kernel; no finite case or global covering theorem.'
    }
    with out.open('x', encoding='utf-8', newline='\n') as f:
        json.dump(result, f, indent=2)
        f.write('\n')
    print(json.dumps(item(out)))


if __name__ == '__main__':
    main()
