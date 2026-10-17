"""Freeze one predeclared point and the exact uniform-budget obstruction."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OUT = HERE/'files.json'


def record(path):
    return {'path': path.relative_to(ROOT).as_posix(), 'bytes': path.stat().st_size,
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


assert not OUT.exists()
r = json.loads((HERE/'receipt.json').read_bytes())
cap = json.loads((HERE/'family-cap.json').read_bytes())
assert record(HERE/'pressure_budget.py')['sha256'] == r['script_sha256']
assert record(HERE/'budget_cap.py')['sha256'] == cap['script_sha256']
assert record(HERE/'receipt.json')['sha256'] == cap['fixed_point_receipt_sha256']
assert r['number_of_continuous_configurations'] == 1
assert r['positive_edge_Taylor_interval_evaluations'] == 41
assert all(row['P_le_c'] and row['all_uniform_affine_pressure_budgets_excluded']
           and Q(row['c_minus_transfer_cap']) > 0 for row in r['target_results'])
assert Q(r['F_fixed_point']['lower']) > Q(221, 25000)
assert Q(cap['pressure']) < Q(cap['T']) == Q(cap['uniform_floor_cap_M'])
assert Q(cap['exact_record_minus_ratio_upper']) > 0
for row in r['pinned_inputs']:
    assert record(ROOT/row['path']) == row
deps = [row['path'] for row in r['pinned_inputs']] + [
 'StructuralGoal20261016/WindowEnergyBound.lean',
 'StructuralGoal20261016/WindowGapEnergy.lean',
 'StructuralGoal20261016/WindowTaylorBridge.lean',
 'StructuralGoal20261016/WindowNormalizedJets.lean',
 'StructuralGoal20261016/WindowJetTableData.lean',
 'StructuralW10Followup20261016/NewLedger.lean',
 'research-goal-20261017-integer-adjacent-floor-audit/audit-files.json',
 'research-goal-20261017-rounding-benefit/files.json',
 'research-goal-20261017-rounding-benefit-independent/audit-files.json',
]
names = ['pressure_budget.py', 'receipt.json', 'budget_cap.py', 'family-cap.json',
         'NOTE.zh.md', 'website-record.json', 'freeze.py']
out = {
 'schema': 'fixed-point-uniform-pressure-budget-files-v1',
 'package_files': [record(HERE/name) for name in names],
 'dependency_files': [record(ROOT/name) for name in sorted(set(deps))],
 'global_uniform_scalar_affine_pressure_family_stopped': True,
 'all_alpha_nonnegative_all_beta_all_valid_uniform_integer_L_covered_on_paper': True,
 'fixed_formal_H_B_interface_cannot_reach_current_record': True,
 'not_an_upper_bound_on_actual_zeta_zero_proportion': True,
 'not_a_counterexample_to_continuous_floor_candidates': True,
 'new_continuous_configurations_evaluated': 1,
 'new_integer_centres': 0, 'new_transcendental_evaluations': 0,
 'optimizer_calls': 0, 'Lean_invocations': 0,
 'new_global_continuous_floor_proven': False,
 'new_unconditional_zero_proportion_proven': False,
 'website_submission_ready': False,
}
OUT.write_text(json.dumps(out, indent=2)+'\n', encoding='utf8')
print(json.dumps({'manifest': record(OUT), 'package_files': len(names),
                  'package_bytes': sum((HERE/name).stat().st_size for name in names)}))
