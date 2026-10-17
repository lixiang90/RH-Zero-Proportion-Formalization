"""Freeze the fixed two-point arithmetic gate without mutable governance inputs."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OUT = HERE/'files.json'


def record(path):
    return {'path': path.relative_to(ROOT).as_posix(),
            'bytes': path.stat().st_size,
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


assert not OUT.exists()
r = json.loads((HERE/'receipt.json').read_bytes())
for row in r['inputs']:
    assert record(ROOT/row['path']) == row
assert r['script_sha256'] == record(HERE/'check.py')['sha256']
assert all(row['argmin'] == 2 for row in r['integer_floor']['rows'])
assert Q(r['integer_floor']['margin_00884']) > 0
assert not r['decoupled_L_and_m_cannot_reach_0088']
assert Q(r['independent_constants_transfer_upper']) > Q(88, 10000)
assert not r['new_Lean'] and not r['new_unconditional_proportion']
refs = [row['path'] for row in r['inputs']] + [
    'StructuralGoal20261016/WindowJetTableData.lean',
    'StructuralGoal20261016/WindowNormalizedJets.lean',
    'StructuralGoal20261016/WindowGapEnergy.lean',
    'StructuralGoal20261016/WindowTaylorBridge.lean',
    'StructuralGoal20261016/WindowRationalInterval.lean',
    'StructuralW10Followup20261016/NewLedger.lean',
    'research-goal-20261017-new24-integer-floor-inventory/files.json',
    'research-goal-20261017-new24-integer-floor-inventory/addendum-files.json',
]
inventory = json.loads((ROOT/refs[-2]).read_bytes())
for row in inventory['reference_inputs']:
    actual = record(ROOT/row['path'])
    assert actual['sha256'] == row['sha256'] and actual['bytes'] == row['bytes']
    refs.append(row['path'])
refs += [f'StructuralGoal20261016/WindowFixedKernelCenter{n:02}.lean'
         for n in range(1, 33)]
files = [HERE/name for name in ['NOTE.zh.md', 'check.py', 'receipt.json', 'freeze.py']]
out = {'schema': 'fixed-common-rounding-benefit-files-v1',
       'package_files': [record(p) for p in files],
       'dependency_files': [record(ROOT/name) for name in sorted(set(refs))],
       'global_positive_integer_floor_on_paper': True,
       'integer_floor_Lean_proven': False,
       'fixed_two_point_no_go_gate_passed': False,
       'uniform_defect_lower_bound_proven': False,
       'new_continuous_global_floor_proven': False,
       'new_unconditional_zero_proportion_proven': False,
       'website_submission_ready': False,
       'solver_calls': 0, 'new_integer_centres': 0, 'Lean_invocations': 0}
OUT.write_text(json.dumps(out, indent=2)+'\n', encoding='utf8')
print(json.dumps({'pin': record(OUT), 'package_files': len(files),
                  'package_bytes': sum(p.stat().st_size for p in files)}))
