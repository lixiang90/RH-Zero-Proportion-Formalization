"""Pure exact postprocessing: cap the entire uniform pressure-budget family."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib
import json

HERE = Path(__file__).resolve().parent
source = HERE/'receipt.json'
r = json.loads(source.read_bytes())
P, T = Q(r['P']), Q(r['transfer_upper_cap'])
M = max(P, T)
H, B, R, K = (Q(r[key]) for key in ['formal_H_lower', 'B', 'record_R', 'goal_K'])
assert P < T < 1 and H > B
ratio_cap = (H-B)/(1-M)
out = {
 'schema': 'uniform-pressure-budget-family-cap-v1',
 'fixed_point_receipt_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
 'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'derivation': 'beta >= -Phi(g*)-alpha*P(g*); L<=Uq; C=(L-deltaB-beta)/(1+alpha) <= (T+alpha*P(g*))/(1+alpha) <= max(T,P(g*)) for every alpha>=0, any real beta, and every valid uniform integer floor L.',
 'pressure': str(P), 'T': str(T), 'uniform_floor_cap_M': str(M),
 'display_uniform_floor_cap': float(M),
 'fixed_H_B_ratio_upper': str(ratio_cap), 'display_ratio_upper_percent': float(100*ratio_cap),
 'exact_record_minus_ratio_upper': str(R-ratio_cap),
 'exact_goal_minus_ratio_upper': str(K-ratio_cap),
 'even_current_record_is_unreachable_by_this_fixed_interface': ratio_cap < R,
 'only_whole_original_domain_uniform_scalar_affine_pressure_defect_budgets': True,
 'actual_continuous_floor_not_refuted': True,
 'new_kernel_evaluations': 0, 'optimizer_calls': 0, 'Lean_invocations': 0,
}
dest = HERE/'family-cap.json'
assert not dest.exists()
dest.write_text(json.dumps(out, indent=2)+'\n', encoding='utf8')
print(json.dumps({k: out[k] for k in ['fixed_point_receipt_sha256', 'display_uniform_floor_cap', 'display_ratio_upper_percent', 'even_current_record_is_unreachable_by_this_fixed_interface']}))
