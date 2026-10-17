"""One fixed point tests all whole-domain affine-pressure defect budgets.

Only existing integer jets and their global Taylor remainder are used.
No optimizer, configuration search, new anchor, or transcendental call.
"""
from pathlib import Path
from fractions import Fraction as Q
from math import factorial
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PINS = {
 'research-20261016-followup/window_reweight_rational.json': '61ad18366b0234d75c4204bc661446c94f1705c29c3e6041bed0147dd6476f11',
 'research-goal-20261016/window_normalized_interval.json': '15e389817127095be26e2ebca6e8bea0d356547a3cb041710029f566cfc13255',
 'research-goal-20261017-ternary-coboundary/support-audit.json': '3d7fc73a21b5f8e8294be0eeb40881a08072412568dd684f7bed785fe1dc24db',
 'research-goal-20261017-rounding-benefit/receipt.json': 'a0d8efb80b7127321e55cef6ac0c956f1bc37d4a183880c0f4efb3d380d9b5e2',
 'research-goal-20261017-fixed-best-point-identity/files.json': '2851d5d85cf8d0ce30125ea207e6041ad93eb6fcf940ee3573f783d6e7a5a24e',
}


def read(path):
    raw = (ROOT/path).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == PINS[path], path
    return json.loads(raw)


def plus(x, y):
    return x[0]+y[0], x[1]+y[1]


def times(x, a):
    return (x[0]*a, x[1]*a) if a >= 0 else (x[1]*a, x[0]*a)


def view(interval):
    return {'lower': str(interval[0]), 'upper': str(interval[1]),
            'display_lower': float(interval[0]), 'display_upper': float(interval[1])}


def main():
    params = read('research-20261016-followup/window_reweight_rational.json')
    data = read('research-goal-20261016/window_normalized_interval.json')
    source = read('research-goal-20261017-ternary-coboundary/support-audit.json')
    old = read('research-goal-20261017-rounding-benefit/receipt.json')
    read('research-goal-20261017-fixed-best-point-identity/files.json')
    gaps = [Q(v) for v in source['zeroV_minimum_sample_exact_binary_float_gaps']]
    assert len(gaps) == 9 and all(g >= Q(123, 128) for g in gaps)
    scale = params['denominator']
    b = [Q(v, scale) for v in params['b_numerators']]
    assert len(b) == 9 and all(v > 0 for v in b)
    a = [(i, j, Q(v, scale)) for i, j, v in params['a_upper'] if v]
    assert len(a) == 41 and all(v > 0 for i, j, v in a)
    jet = {int(n): [tuple(Q(v) for v in row) for row in coeffs]
           for n, coeffs in data['integer_w_Taylor_coefficients'].items()}
    assert all(len(v) == 24 for v in jet.values())
    delta, B = Q(5, 128), sum(b)
    P = sum(bi*gi for bi, gi in zip(b, gaps))
    H = Q(6720963398090236473924, 10**22)
    R = Q(34191001116882886388531117129201664, 50760020691785094633026544189453125)
    K = R+Q(1, 100000)
    c_required = 1-(H-B)/K
    targets = [('record_plus_1e-5_with_current_formal_H', c_required),
               ('lower_candidate', Q(11, 1250)), ('higher_candidate', Q(221, 25000))]
    # Before evaluating any polynomial, verify the predeclared pressure gate.
    assert P <= c_required
    q_interval = tuple(Q(old['F_q'][key]) for key in ['lower', 'upper'])
    assert old['fixed_configurations']['integer_q_all_gaps'] == '2'
    assert Q(old['B']) == B and Q(old['delta']) == delta
    Uq = q_interval[1]
    prefix = [Q(0)]
    for g in gaps:
        prefix.append(prefix[-1]+g)
    phi, Fg = (Q(0), Q(0)), (P, P)
    rows = []
    for i, j, weight in a:
        z, d = prefix[j]-prefix[i], j-i
        centre = (z+Q(1, 2)).numerator // (z+Q(1, 2)).denominator
        assert 1 <= centre <= 32
        x = z-centre
        value = (Q(0), Q(0))
        for coefficient in reversed(jet[centre]):
            value = plus(times(value, x), coefficient)
        remainder = Q(44, 7)**24*abs(x)**24/factorial(24)
        actual = value[0]-remainder, value[1]+remainder
        t = z+d*delta
        n = t.numerator // t.denominator
        u = t-n
        assert 1 <= n and n+1 <= 32
        interpolation = plus(times(jet[n][0], 1-u), times(jet[n+1][0], u))
        defect = actual[0]-interpolation[1], actual[1]-interpolation[0]
        phi = plus(phi, times(defect, weight))
        Fg = plus(Fg, times(actual, weight))
        rows.append({'pair': [i, j], 'weight': str(weight), 'z': str(z),
                     'centre': centre, 'offset': str(x), 'remainder': str(remainder),
                     'w_interval': view(actual), 'interpolation_argument': str(t),
                     'interpolation_floor': n, 'interpolation_fraction': str(u),
                     'interpolation_interval': view(interpolation),
                     'defect_interval': view(defect)})
    transfer_cap = Uq-delta*B+phi[1]
    result = {
      'schema': 'one-fixed-point-affine-pressure-budget-obstruction-v1',
      'scope': __doc__,
      'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'pinned_inputs': [{'path': path, 'sha256': sha, 'bytes': (ROOT/path).stat().st_size}
                        for path, sha in PINS.items()],
      'point_source_field': 'zeroV_minimum_sample_exact_binary_float_gaps',
      'fixed_gaps': [str(g) for g in gaps],
      'domain_s': '123/128', 'P': str(P), 'display_P': float(P),
      'B': str(B), 'delta': str(delta), 'delta_B': str(delta*B),
      'formal_H_lower': str(H), 'record_R': str(R), 'goal_K': str(K),
      'integer_uniform_L_cap_F_all2': view(q_interval),
      'Phi_fixed_point': view(phi), 'F_fixed_point': view(Fg),
      'transfer_upper_cap': str(transfer_cap), 'display_transfer_upper_cap': float(transfer_cap),
      'target_results': [{'name': name, 'c': str(c), 'display_c': float(c),
                          'P_le_c': P <= c, 'c_minus_transfer_cap': str(c-transfer_cap),
                          'display_c_minus_transfer_cap': float(c-transfer_cap),
                          'all_uniform_affine_pressure_budgets_excluded': P <= c and transfer_cap < c}
                         for name, c in targets],
      'number_of_continuous_configurations': 1, 'positive_edge_Taylor_interval_evaluations': len(rows),
      'new_integer_centres': 0, 'new_transcendental_evaluations': 0,
      'optimizer_calls': 0, 'Lean_invocations': 0,
      'excludes_only_whole_original_domain_uniform_scalar_affine_pressure_budget': True,
      'does_not_refute_continuous_floor_or_minimizer_conditioned_budgets': True,
      'new_continuous_floor_proven': False, 'new_unconditional_proportion_proven': False,
      'rows': rows,
    }
    dest = HERE/'receipt.json'
    assert not dest.exists(), 'Never overwrite a fixed gate receipt'
    dest.write_text(json.dumps(result, indent=2)+'\n', encoding='utf8')
    print(json.dumps({key: result[key] for key in ['display_P', 'F_fixed_point', 'Phi_fixed_point',
                     'display_transfer_upper_cap', 'target_results']}, ensure_ascii=False))


if __name__ == '__main__':
    main()
