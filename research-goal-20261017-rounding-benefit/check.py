"""One fixed exact benefit gate, using saved jets only; no kernel/solver calls.

The two predeclared configurations are nine gaps all 2 and all 21/20.
This is not a floor proof and not a search for better configurations.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import factorial
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PARAM = 'research-20261016-followup/window_reweight_rational.json'
JETS = 'research-goal-20261016/window_normalized_interval.json'
PINS = {
    PARAM: '61ad18366b0234d75c4204bc661446c94f1705c29c3e6041bed0147dd6476f11',
    JETS: '15e389817127095be26e2ebca6e8bea0d356547a3cb041710029f566cfc13255',
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def add(x, y):
    return x[0]+y[0], x[1]+y[1]


def mul(x, q):
    return (x[0]*q, x[1]*q) if q >= 0 else (x[1]*q, x[0]*q)


def output_interval(x):
    return {'lower': str(x[0]), 'upper': str(x[1]),
            'display_lower': float(x[0]), 'display_upper': float(x[1])}


def main():
    for path, expected in PINS.items():
        assert sha(ROOT/path) == expected, path
    p = json.loads((ROOT/PARAM).read_bytes())
    j = json.loads((ROOT/JETS).read_bytes())
    assert j['parameter_sha256'] == PINS[PARAM]
    denominator = p['denominator']
    a = {(i, k): Q(v, denominator) for i, k, v in p['a_upper']}
    b = [Q(v, denominator) for v in p['b_numerators']]
    assert len(b) == 9 and all(v > 0 for v in b)
    assert len(a) == 45 and sum(v > 0 for v in a.values()) == 41
    assert all(v >= 0 for v in a.values())
    B = sum(b)
    delta = Q(5, 128)
    jet = {int(n): [tuple(Q(v) for v in entry) for entry in coeffs]
           for n, coeffs in j['integer_w_Taylor_coefficients'].items()}
    assert set(jet) == set(range(33))
    assert all(len(v) == 24 for v in jet.values())
    assert all(lo <= hi for coeffs in jet.values() for lo, hi in coeffs)

    # Existing integer values + positivity of w handle the entire integer tail.
    rows = []
    for r, pressure in enumerate(b):
        candidates = [(pressure*n + a[r, r+1]*jet[n][0][0], n)
                      for n in range(1, 33)]
        candidates.append((33*pressure, 'n>=33: w>=0'))
        value, arg = min(candidates, key=lambda pair: pair[0])
        rows.append({'gap': r, 'argmin': arg, 'lower': str(value),
                     'tail_lower': str(33*pressure)})
    L_adj = sum(Q(row['lower']) for row in rows)

    eval_rows = []

    def w_interval(z):
        # Nearest integer fixed by exact rational arithmetic (no tie here).
        n = (z+Q(1, 2)).numerator // (z+Q(1, 2)).denominator
        assert 1 <= n <= 32
        x = z-n
        value = (Q(0), Q(0))
        for entry in reversed(jet[n]):
            value = add(mul(value, x), entry)
        remainder = Q(44, 7)**24 * abs(x)**24 / factorial(24)
        answer = value[0]-remainder, value[1]+remainder
        eval_rows.append({'z': str(z), 'centre': n, 'offset': str(x),
                          'remainder': str(remainder),
                          'bound': output_interval(answer)})
        return answer

    q_gap, g_gap = Q(2), Q(21, 20)
    q_energy = (q_gap*B, q_gap*B)
    phi = (Q(0), Q(0))
    edge_rows = []
    for (i, k), weight in a.items():
        if weight == 0:
            continue
        d = k-i
        q_energy = add(q_energy, mul(jet[2*d][0], weight))
        z = d*g_gap
        t = z+d*delta
        n = t.numerator // t.denominator
        u = t-n
        assert 1 <= n and n+1 <= 32
        interpolated = add(mul(jet[n][0], 1-u), mul(jet[n+1][0], u))
        actual = w_interval(z)
        defect = actual[0]-interpolated[1], actual[1]-interpolated[0]
        phi = add(phi, mul(defect, weight))
        edge_rows.append({'pair': [i, k], 'weight': str(weight), 'z': str(z),
                          't': str(t), 'interpolation_floor': n,
                          'interpolation_fraction': str(u),
                          'defect_interval': output_interval(defect)})
    transfer_upper = q_energy[1]-delta*B+phi[1]
    out = {
        'schema': 'fixed-common-rounding-benefit-gate-v1',
        'scope': __doc__,
        'inputs': [{'path': path, 'sha256': sha(ROOT/path),
                    'bytes': (ROOT/path).stat().st_size} for path in [PARAM, JETS]],
        'script_sha256': sha(Path(__file__)),
        'integer_floor': {'rows': rows, 'L_adj': str(L_adj),
                          'display': float(L_adj),
                          'positive_gap_integer_domain_complete_on_paper': True,
                          'new_Lean_theorem': False,
                          'margin_0088': str(L_adj-Q(88, 10000)),
                          'margin_00884': str(L_adj-Q(884, 100000))},
        'fixed_configurations': {'integer_q_all_gaps': str(q_gap),
                                 'continuous_g_all_gaps': str(g_gap),
                                 'continuous_g_need_not_be_minimizer': True},
        'B': str(B), 'delta': str(delta), 'pressure_payment': str(delta*B),
        'F_q': output_interval(q_energy), 'Phi_g': output_interval(phi),
        'independent_constants_transfer_upper': str(transfer_upper),
        'display_transfer_upper': float(transfer_upper),
        'target_0088_minus_upper': str(Q(88, 10000)-transfer_upper),
        'decoupled_L_and_m_cannot_reach_0088': transfer_upper < Q(88, 10000),
        'does_not_exclude_coupled_transfer_or_different_rounding': True,
        'edge_rows': edge_rows, 'taylor_evaluations': eval_rows,
        'new_integer_centres': 0, 'new_transcendental_evaluations': 0,
        'optimizer_calls': 0, 'new_Lean': False,
        'new_unconditional_proportion': False,
    }
    (HERE/'receipt.json').write_text(json.dumps(out, ensure_ascii=False, indent=2)+'\n', encoding='utf8')
    print(json.dumps({k: out[k] for k in ['integer_floor', 'F_q', 'Phi_g',
                     'display_transfer_upper', 'decoupled_L_and_m_cannot_reach_0088']},
                     ensure_ascii=False))


if __name__ == '__main__':
    main()
