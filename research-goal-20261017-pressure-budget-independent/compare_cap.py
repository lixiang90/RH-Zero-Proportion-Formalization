"""Pure Fraction comparison of the producer's later family-cap postprocessing."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PINS = {
 'research-goal-20261017-pressure-budget/family-cap.json': '68fbb5b1e77744be6d8a10f4bdf66bbf47bbb311e33d3e33839fd9db5e7b5f75',
 'research-goal-20261017-pressure-budget/budget_cap.py': 'f87ec95296c0204090f063809425a614246e71c4e89dd76202d7b67f65fc5ea9',
 'research-goal-20261017-pressure-budget/receipt.json': '640c93ffa7cc4f2f460ba4c4d86ca49604c05cc74b036a39538f4c3d26cac373',
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


for path, expected in PINS.items():
    assert sha(ROOT/path) == expected
saved = json.loads((ROOT/'research-goal-20261017-pressure-budget/family-cap.json').read_bytes())
independent = json.loads((HERE/'receipt.json').read_bytes())
assert independent['replay_passed']
assert sha(HERE/'replay.py') == independent['script_sha256']
assert saved['fixed_point_receipt_sha256'] == PINS['research-goal-20261017-pressure-budget/receipt.json']
assert saved['script_sha256'] == PINS['research-goal-20261017-pressure-budget/budget_cap.py']
P, T = Q(independent['P']), Q(independent['uniform_budget_floor_cap'])
H, B = Q(independent['fixed_H']), Q(independent['B'])
R, K = Q(independent['record_R']), Q(independent['goal_K'])
ratio = (H-B)/(1-max(P, T))
assert P < T < 1 and H > B and ratio < R < K
assert Q(saved['pressure']) == P
assert Q(saved['T']) == Q(saved['uniform_floor_cap_M']) == T
assert Q(saved['fixed_H_B_ratio_upper']) == Q(independent['fixed_H_counting_coefficient_cap']) == ratio
assert Q(saved['exact_record_minus_ratio_upper']) == R-ratio
assert Q(saved['exact_goal_minus_ratio_upper']) == K-ratio
assert saved['even_current_record_is_unreachable_by_this_fixed_interface']
out = {
 'schema': 'independent-pressure-family-cap-comparison-v1',
 'passed': True, 'all_compared_rational_fields_exactly_equal': True,
 'uniform_floor_cap': str(T), 'fixed_H_B_counting_coefficient_cap': str(ratio),
 'exact_record_minus_coefficient_cap': str(R-ratio),
 'exact_goal_minus_coefficient_cap': str(K-ratio),
 'coefficient_cap_is_not_an_actual_zeta_proportion_upper_bound': True,
 'producer_float_fields_used_in_arithmetic': False,
 'pinned_inputs': [{'path': path, 'sha256': expected} for path, expected in PINS.items()],
 'independent_receipt_sha256': sha(HERE/'receipt.json'),
 'independent_replay_script_sha256': sha(HERE/'replay.py'),
 'script_sha256': sha(Path(__file__)),
 'new_points': 0, 'new_kernel_evaluations': 0, 'optimizer_calls': 0, 'Lean_invocations': 0,
}
destination = HERE/'cap-comparison.json'
assert not destination.exists()
destination.write_text(json.dumps(out, indent=2)+'\n', encoding='utf8')
print(json.dumps({'passed': True, 'all_compared_rational_fields_exactly_equal': True,
                  'fixed_H_B_coefficient_cap_strictly_below_record': True}))
