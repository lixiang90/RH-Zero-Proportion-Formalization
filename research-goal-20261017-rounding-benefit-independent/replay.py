"""Independent replay of exactly the two predeclared common-rounding points.

Uses the frozen integer-centre interval table and Fraction only. Grouping
edges by distance and summing Taylor powers replaces the producer's edgewise
Horner evaluation. No new anchor, kernel evaluation, optimization, or scan.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import factorial
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PINS = {
    'research-goal-20261017-rounding-benefit/check.py': 'a7884abe0db3da5750ef05b0e1920526304f1f0ff78392f4b9201c1b84fa96cd',
    'research-goal-20261017-rounding-benefit/receipt.json': 'a0d8efb80b7127321e55cef6ac0c956f1bc37d4a183880c0f4efb3d380d9b5e2',
    'research-20261016-followup/window_reweight_rational.json': '61ad18366b0234d75c4204bc661446c94f1705c29c3e6041bed0147dd6476f11',
    'research-goal-20261016/window_normalized_interval.json': '15e389817127095be26e2ebca6e8bea0d356547a3cb041710029f566cfc13255',
    'StructuralGoal20261016/WindowTaylorBridge.lean': 'b3db359086705edb1b5552106248bdd2e5aac6dae6333b4e4cc72f48855bda24',
    'StructuralGoal20261016/WindowRawCoefficients.lean': '6d1511d7024916b0dce4805b913e31b7a42f75a8488e4fb6054e6fd6a680916d',
    'StructuralGoal20261016/WindowNormalizedJets.lean': '8b47725eb97a47e0a86294a771cfb06a9fc299e4a0a7e7edf4410885cb01b6cc',
    'StructuralW10Followup20261016/NewLedger.lean': '9db3e7633a3117f4fded88998da4ab3ebc4e24631ac50816f23931bdb8225d1a',
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def interval_record(value):
    return {'lower': str(value[0]), 'upper': str(value[1]),
            'display_lower': float(value[0]), 'display_upper': float(value[1])}


def matches(value, saved):
    assert value == (Q(saved['lower']), Q(saved['upper']))


def main():
    for path, expected in PINS.items():
        assert sha(ROOT/path) == expected, path
    saved = json.loads((ROOT/'research-goal-20261017-rounding-benefit/receipt.json').read_bytes())
    param = json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    table = json.loads((ROOT/'research-goal-20261016/window_normalized_interval.json').read_bytes())
    assert table['parameter_sha256'] == PINS['research-20261016-followup/window_reweight_rational.json']
    denominator = param['denominator']
    assert denominator == 10**10
    a = {(i, j): Q(v, denominator) for i, j, v in param['a_upper']}
    b = [Q(v, denominator) for v in param['b_numerators']]
    assert len(a) == 45 and len(b) == 9
    assert all(i < j <= 9 and weight >= 0 for (i, j), weight in a.items())
    assert all(weight > 0 for weight in b)

    # Match the JSON ledger to its actual Lean coefficient source, by literals.
    ledger = (ROOT/'StructuralW10Followup20261016/NewLedger.lean').read_text(encoding='utf8')
    a_text, b_text = ledger.split('def aN', 1)[1].split('def bN', 1)
    b_text = b_text.split('def a ', 1)[0]
    a_lean = {(int(i), int(j)): Q(int(v), denominator)
              for i, j, v in re.findall(r'\|\s*(\d+),\s*(\d+)\s*=>\s*(\d+)', a_text)}
    b_lean = {int(i): Q(int(v), denominator)
              for i, v in re.findall(r'\|\s*(\d+)\s*=>\s*(\d+)', b_text)}
    assert a == a_lean and b == [b_lean[i] for i in range(9)]
    jet = {int(n): [(Q(lo), Q(hi)) for lo, hi in entries]
           for n, entries in table['integer_w_Taylor_coefficients'].items()}
    assert set(jet) == set(range(33))
    assert all(len(entries) == 24 and all(lo <= hi for lo, hi in entries)
               for entries in jet.values())

    B, delta, separation = sum(b), Q(5, 128), Q(123, 128)
    assert separation + delta == 1 and Q(21, 20) > separation
    assert B == Q(11055671, 2500000000) == Q(saved['B'])
    assert delta*B == Q(saved['pressure_payment'])
    distance_mass = {d: sum(weight for (i, j), weight in a.items() if j-i == d)
                     for d in range(1, 10)}

    # The declared integer candidate n=2 is checked against the fixed 1..32
    # table and the whole n>=33 tail; this is not an anchor discovery step.
    adjacent_rows = []
    for r in range(9):
        candidate = 2*b[r] + a[r, r+1]*jet[2][0][0]
        assert all(candidate <= n*b[r] + a[r, r+1]*jet[n][0][0]
                   for n in range(1, 33))
        assert candidate <= 33*b[r]
        assert candidate == Q(saved['integer_floor']['rows'][r]['lower'])
        assert saved['integer_floor']['rows'][r]['argmin'] == 2
        adjacent_rows.append(candidate)
    L_adj = sum(adjacent_rows)
    assert L_adj == Q(saved['integer_floor']['L_adj'])
    assert L_adj > Q(884, 100000) > Q(88, 10000)

    q_value = tuple(2*B + sum(distance_mass[d]*jet[2*d][0][end]
                              for d in range(1, 10)) for end in (0, 1))
    phi = [Q(0), Q(0)]
    distance_rows = []
    values_by_distance = {}
    for d in range(1, 10):
        x, z = Q(d, 20), Q(21*d, 20)
        fraction = Q(57*d, 640)
        t = Q(697*d, 640)
        assert z == d+x and 0 < x < Q(1, 2)
        assert t == z+d*delta == d+fraction and 0 < fraction < 1
        assert t.numerator // t.denominator == d
        remainder = (Q(44, 7)*x)**24 / factorial(24)
        actual = (sum(jet[d][r][0]*x**r for r in range(24))-remainder,
                  sum(jet[d][r][1]*x**r for r in range(24))+remainder)
        interpolated = tuple((1-fraction)*jet[d][0][end]
                             + fraction*jet[d+1][0][end] for end in (0, 1))
        defect = (actual[0]-interpolated[1], actual[1]-interpolated[0])
        for end in (0, 1):
            phi[end] += distance_mass[d]*defect[end]
        values_by_distance[d] = actual, defect, remainder
        distance_rows.append({'distance': d, 'mass': str(distance_mass[d]),
                              'z': str(z), 'centre': d, 'offset': str(x),
                              'interpolation_t': str(t), 'fraction': str(fraction),
                              'actual': interval_record(actual),
                              'defect': interval_record(defect)})
    phi = tuple(phi)
    matches(q_value, saved['F_q'])
    matches(phi, saved['Phi_g'])
    for row in saved['edge_rows']:
        i, j = row['pair']
        d = j-i
        assert a[i, j] == Q(row['weight']) > 0
        assert Q(row['z']) == Q(21*d, 20)
        assert Q(row['t']) == Q(697*d, 640)
        assert row['interpolation_floor'] == d
        assert Q(row['interpolation_fraction']) == Q(57*d, 640)
        matches(values_by_distance[d][1], row['defect_interval'])
    assert len(saved['edge_rows']) == sum(weight > 0 for weight in a.values()) == 41
    assert len(saved['taylor_evaluations']) == 41
    for row in saved['taylor_evaluations']:
        d = Q(row['z']) / Q(21, 20)
        assert d.denominator == 1 and 1 <= d <= 9
        d = int(d)
        assert row['centre'] == d and Q(row['offset']) == Q(d, 20)
        assert Q(row['remainder']) == values_by_distance[d][2]
        matches(values_by_distance[d][0], row['bound'])
    transfer = (q_value[0]-delta*B+phi[0], q_value[1]-delta*B+phi[1])
    assert transfer[1] == Q(saved['independent_constants_transfer_upper'])
    no_go_0088 = transfer[1] < Q(88, 10000)
    assert no_go_0088 == saved['decoupled_L_and_m_cannot_reach_0088'] == False
    assert transfer[0] > Q(884, 100000)

    result = {
        'schema': 'fixed-common-rounding-benefit-independent-replay-v1',
        'replay_passed': True,
        'no_go_logic_correct_for_uniform_independent_constants': True,
        'fixed_pair_proves_no_go': False,
        'false_result_does_not_prove_method_success_or_failure': True,
        'F_q': interval_record(q_value), 'Phi_g': interval_record(phi),
        'fixed_expression_Fq_minus_deltaB_plus_Phi': interval_record(transfer),
        'entire_fixed_expression_interval_above_00884': True,
        'integer_floor_L_adj': str(L_adj),
        'integer_floor_complete_on_paper_using_saved_intervals': True,
        'new_Lean_theorem': False,
        'distance_rows': distance_rows,
        'ledger_matches_actual_Lean_literals': True,
        'existing_table_analytic_soundness_recompiled': False,
        'inputs': [{'path': path, 'sha256': expected, 'bytes': (ROOT/path).stat().st_size}
                   for path, expected in PINS.items()],
        'script_sha256': sha(Path(__file__)),
        'new_points_or_anchors': 0, 'new_transcendental_evaluations': 0,
        'optimizer_calls': 0, 'cover_tree_scans': 0, 'Lean_compilations': 0,
        'unconditional_record_proved': False,
    }
    (HERE/'receipt.json').write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n', encoding='utf8')
    print(json.dumps({key: result[key] for key in (
        'replay_passed', 'fixed_pair_proves_no_go', 'F_q', 'Phi_g',
        'fixed_expression_Fq_minus_deltaB_plus_Phi', 'integer_floor_L_adj')}, ensure_ascii=False))


if __name__ == '__main__':
    main()
