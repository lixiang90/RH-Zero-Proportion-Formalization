"""Independent fixed-point replay for whole-domain pressure-affine budgets.

No producer import or discovery. Sum signed Taylor powers at each distinct
saved span, aggregate equal spans and interpolation weights, then replay all
producer edge endpoints. Only Fraction and frozen files are used.
"""
from collections import defaultdict
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PINS = {
 'research-goal-20261017-pressure-budget/pressure_budget.py': '029fe3593d22f4b63d4b0d22fba7c643013a44dab99160aba2894d5c0a99841b',
 'research-goal-20261017-pressure-budget/receipt.json': '640c93ffa7cc4f2f460ba4c4d86ca49604c05cc74b036a39538f4c3d26cac373',
 'research-20261016-followup/window_reweight_rational.json': '61ad18366b0234d75c4204bc661446c94f1705c29c3e6041bed0147dd6476f11',
 'research-goal-20261016/window_normalized_interval.json': '15e389817127095be26e2ebca6e8bea0d356547a3cb041710029f566cfc13255',
 'research-goal-20261017-ternary-coboundary/support-audit.json': '3d7fc73a21b5f8e8294be0eeb40881a08072412568dd684f7bed785fe1dc24db',
 'research-goal-20261017-rounding-benefit/receipt.json': 'a0d8efb80b7127321e55cef6ac0c956f1bc37d4a183880c0f4efb3d380d9b5e2',
 'research-goal-20261017-fixed-best-point-identity/files.json': '2851d5d85cf8d0ce30125ea207e6041ad93eb6fcf940ee3573f783d6e7a5a24e',
 'StructuralW10Followup20261016/NewLedger.lean': '9db3e7633a3117f4fded88998da4ab3ebc4e24631ac50816f23931bdb8225d1a',
 'StructuralGoal20261016/WindowGapEnergy.lean': '3f570bc83263355a239c086922e9bc138319fd2abd77668b594b5f94a5fd6564',
 'StructuralGoal20261016/WindowTaylorBridge.lean': 'b3db359086705edb1b5552106248bdd2e5aac6dae6333b4e4cc72f48855bda24',
 'StructuralGoal20261016/WindowRawCoefficients.lean': '6d1511d7024916b0dce4805b913e31b7a42f75a8488e4fb6054e6fd6a680916d',
 'StructuralGoal20261016/WindowNormalizedJets.lean': '8b47725eb97a47e0a86294a771cfb06a9fc299e4a0a7e7edf4410885cb01b6cc',
 'StructuralGoal20261016/WindowEnergyBound.lean': '29bb4a9ab7c8cbdd0c067993241d093999fdc63a983102968a74c23850dd8e14',
 'StructuralGoal20261016/WindowRecordLowerFloor.lean': '518379640c1841340703cf3bfbbab427a21a4adcb798f5cd31dabd5fbf5fa605',
 'research-goal-20261017-common-rounding-independent/NOTE.zh.md': '11c37475e495007e460c2b35dbc21265a2e94c54d28049e39e1e048890113ffd',
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads((ROOT/path).read_bytes())


def record(value):
    return {'lower': str(value[0]), 'upper': str(value[1]),
            'display_lower': float(value[0]), 'display_upper': float(value[1])}


def equal_interval(value, saved):
    assert value == (Q(saved['lower']), Q(saved['upper']))


def main():
    for path, expected in PINS.items():
        assert sha(ROOT/path) == expected, path
    producer = load('research-goal-20261017-pressure-budget/receipt.json')
    param = load('research-20261016-followup/window_reweight_rational.json')
    table = load('research-goal-20261016/window_normalized_interval.json')
    source = load('research-goal-20261017-ternary-coboundary/support-audit.json')
    old = load('research-goal-20261017-rounding-benefit/receipt.json')
    identity_manifest = load('research-goal-20261017-fixed-best-point-identity/files.json')
    for item in identity_manifest['files']:
        assert sha(ROOT/item['path']) == item['sha256']
    identity = load('research-goal-20261017-fixed-best-point-identity/identity-replay.json')
    assert identity['passed'] and identity['all_9_existing_rationals_equal_saved_binary_floats']
    gap_strings = source['zeroV_minimum_sample_exact_binary_float_gaps']
    assert gap_strings == identity['fixed_point']['values'] == producer['fixed_gaps']
    gaps = [Q(value) for value in gap_strings]
    assert len(gaps) == 9 and all(value >= Q(123, 128) for value in gaps)
    assert table['parameter_sha256'] == PINS['research-20261016-followup/window_reweight_rational.json']
    denominator = param['denominator']
    assert denominator == 10**10
    a = {(i, j): Q(value, denominator) for i, j, value in param['a_upper']}
    b = [Q(value, denominator) for value in param['b_numerators']]
    assert len(a) == 45 and len(b) == 9
    assert all(0 <= i < j <= 9 and value >= 0 for (i, j), value in a.items())
    assert sum(value > 0 for value in a.values()) == 41 and all(value > 0 for value in b)
    ledger = (ROOT/'StructuralW10Followup20261016/NewLedger.lean').read_text(encoding='utf8')
    a_text, b_text = ledger.split('def aN', 1)[1].split('def bN', 1)
    b_text = b_text.split('def a ', 1)[0]
    a_lean = {(int(i), int(j)): Q(int(value), denominator)
              for i, j, value in re.findall(r'\|\s*(\d+),\s*(\d+)\s*=>\s*(\d+)', a_text)}
    b_lean = {int(i): Q(int(value), denominator)
              for i, value in re.findall(r'\|\s*(\d+)\s*=>\s*(\d+)', b_text)}
    assert a == a_lean and b == [b_lean[i] for i in range(9)]
    B, delta = sum(b), Q(5, 128)
    P = sum(b[r]*gaps[r] for r in range(9))
    assert B == Q(11055671, 2500000000) == Q(producer['B'])
    assert P == Q(producer['P']) and delta*B == Q(producer['delta_B'])
    jet = {int(n): [(Q(lo), Q(hi)) for lo, hi in entries]
           for n, entries in table['integer_w_Taylor_coefficients'].items()}
    assert set(jet) == set(range(33))
    assert all(len(entries) == 24 and all(lo <= hi for lo, hi in entries)
               for entries in jet.values())

    # Group by exact span before any Taylor arithmetic; interpolate separately.
    span_mass, interpolation_mass = defaultdict(Q), defaultdict(Q)
    edge_info = {}
    for (i, j), weight in a.items():
        if weight == 0:
            continue
        z = sum(gaps[i:j])
        d = j-i
        t = z+d*delta
        n = t.numerator // t.denominator
        u = t-n
        assert 1 <= n < 32 and 0 <= u < 1
        span_mass[z] += weight
        interpolation_mass[n] += weight*(1-u)
        interpolation_mass[n+1] += weight*u
        edge_info[i, j] = z, t, n, u

    values = {}
    for z in span_mass:
        # Exact nearest-integer centre, then independent signed power summation.
        n = (2*z.numerator+z.denominator) // (2*z.denominator)
        x = z-n
        assert 1 <= n <= 32 and -Q(1, 2) < x < Q(1, 2)
        value = [Q(0), Q(0)]
        for degree, (lo, hi) in enumerate(jet[n]):
            power = x**degree
            value[0] += (lo if power >= 0 else hi)*power
            value[1] += (hi if power >= 0 else lo)*power
        remainder = (Q(44, 7)*abs(x))**24/factorial(24)
        actual = value[0]-remainder, value[1]+remainder
        values[z] = n, x, remainder, actual
    actual_sum = tuple(sum(weight*values[z][3][end] for z, weight in span_mass.items())
                       for end in (0, 1))
    interpolation_sum = tuple(sum(weight*jet[n][0][end]
                                  for n, weight in interpolation_mass.items())
                              for end in (0, 1))
    phi = actual_sum[0]-interpolation_sum[1], actual_sum[1]-interpolation_sum[0]
    Fg = P+actual_sum[0], P+actual_sum[1]
    equal_interval(phi, producer['Phi_fixed_point'])
    equal_interval(Fg, producer['F_fixed_point'])
    assert len(producer['rows']) == len(edge_info) == 41
    seen_pairs = set()
    for row in producer['rows']:
        i, j = row['pair']
        assert (i, j) not in seen_pairs
        seen_pairs.add((i, j))
        z, t, n, u = edge_info[i, j]
        centre, x, remainder, actual = values[z]
        interp = tuple((1-u)*jet[n][0][end]+u*jet[n+1][0][end] for end in (0, 1))
        defect = actual[0]-interp[1], actual[1]-interp[0]
        assert Q(row['weight']) == a[i, j]
        assert Q(row['z']) == z and row['centre'] == centre
        assert Q(row['offset']) == x and Q(row['remainder']) == remainder
        assert Q(row['interpolation_argument']) == t
        assert row['interpolation_floor'] == n and Q(row['interpolation_fraction']) == u
        equal_interval(actual, row['w_interval'])
        equal_interval(interp, row['interpolation_interval'])
        equal_interval(defect, row['defect_interval'])

    # Independently replay the already fixed all-2 integer cap from zero jets.
    distance_mass = {d: sum(weight for (i, j), weight in a.items() if j-i == d)
                     for d in range(1, 10)}
    q_value = tuple(2*B+sum(distance_mass[d]*jet[2*d][0][end] for d in range(1, 10))
                    for end in (0, 1))
    equal_interval(q_value, old['F_q'])
    equal_interval(q_value, producer['integer_uniform_L_cap_F_all2'])
    T = q_value[1]-delta*B+phi[1]
    assert T == Q(producer['transfer_upper_cap'])
    assert P < T < 1

    H = Q(6720963398090236473924, 10**22)
    R = Q(34191001116882886388531117129201664, 50760020691785094633026544189453125)
    K = R+Q(1, 100000)
    c_required = 1-(H-B)/K
    assert H == Q(producer['formal_H_lower']) and R == Q(producer['record_R'])
    assert K == Q(producer['goal_K']) and H > B
    H_source = (ROOT/'StructuralGoal20261016/WindowEnergyBound.lean').read_text(encoding='utf8')
    assert 'theorem H24_ge : (6720963398090236473924 / 10 ^ 22 : ℝ)' in H_source
    counting_source = (ROOT/'StructuralGoal20261016/WindowRecordLowerFloor.lean').read_text(encoding='utf8')
    assert '34191001116882886388531117129201664' in counting_source
    assert '50760020691785094633026544189453125' in counting_source
    assert ')/(1-11/1250)' in counting_source
    targets = [('record_plus_1e-5_with_current_formal_H', c_required),
               ('lower_candidate', Q(11, 1250)), ('higher_candidate', Q(221, 25000))]
    target_rows = []
    assert len(producer['target_results']) == 3
    for (name, c), saved in zip(targets, producer['target_results']):
        assert name == saved['name'] and c == Q(saved['c'])
        assert P <= c and T < c and c-T == Q(saved['c_minus_transfer_cap'])
        assert saved['all_uniform_affine_pressure_budgets_excluded']
        assert Fg[0] > c
        target_rows.append({'name': name, 'c': str(c), 'display_c': float(c),
                            'pressure_margin': str(c-P), 'floor_cap_margin': str(c-T),
                            'display_floor_cap_margin': float(c-T),
                            'uniform_pressure_affine_budget_excluded': True,
                            'actual_fixed_point_is_not_floor_counterexample': True})
    proportion_coefficient_cap = (H-B)/(1-T)
    assert proportion_coefficient_cap < K
    result = {
      'schema': 'independent-fixed-pressure-affine-budget-replay-v1',
      'replay_passed': True,
      'scope': 'Only the full-original-domain scalar affine-pressure defect budget and independent uniform integer floor interface; not minimizer/sublevel-conditioned or coupled-support budgets, actual floor falsity, or actual zeta proportion upper bounds.',
      'implementation': 'Aggregate equal exact spans and integer interpolation weights; signed direct Taylor-power summation; no producer imports.',
      'fixed_point_source': {'path': 'research-goal-20261017-ternary-coboundary/support-audit.json',
                             'field': 'zeroV_minimum_sample_exact_binary_float_gaps',
                             'gaps': gap_strings, 'unchanged': True},
      'ledger_matches_Lean_literals': True, 'edge_records_replayed': 41,
      'distinct_existing_spans': len(span_mass),
      'P': str(P), 'display_P': float(P), 'B': str(B), 'delta_B': str(delta*B),
      'F_all2': record(q_value), 'Phi_fixed_point': record(phi), 'F_fixed_point': record(Fg),
      'uniform_budget_floor_cap': str(T), 'display_uniform_budget_floor_cap': float(T),
      'pressure_strictly_below_family_cap': True,
      'family_cap_formula': 'C=(L-delta*B-beta)/(1+alpha) <= (T+alpha*P)/(1+alpha) <= max(T,P)=T',
      'alpha_domain': 'all real alpha>=0', 'beta_domain': 'all real beta',
      'integer_L_domain': 'every valid uniform integer floor L, including the best; L<=F(all2)<=Uq',
      'target_results': target_rows,
      'fixed_H': str(H), 'record_R': str(R), 'goal_K': str(K),
      'fixed_H_counting_coefficient_cap': str(proportion_coefficient_cap),
      'display_fixed_H_counting_coefficient_cap': float(proportion_coefficient_cap),
      'fixed_H_coefficient_cap_strictly_below_goal': True,
      'coefficient_cap_is_not_actual_zeta_proportion_upper_bound': True,
      'pinned_inputs': [{'path': path, 'sha256': expected, 'bytes': (ROOT/path).stat().st_size}
                        for path, expected in PINS.items()],
      'identity_manifest_member_hashes_verified': True,
      'script_sha256': sha(Path(__file__)),
      'points_beyond_the_one_predeclared_continuous_point_and_saved_all2_cap': 0,
      'new_transcendental_evaluations': 0, 'optimizer_calls': 0, 'cover_tree_scans': 0,
      'Lean_compilations': 0, 'new_Lean_theorem': False,
      'new_continuous_floor_proven': False, 'new_unconditional_proportion_proven': False,
    }
    destination = HERE/'receipt.json'
    assert not destination.exists(), 'Never overwrite the independent fixed gate receipt'
    destination.write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n', encoding='utf8')
    print(json.dumps({key: result[key] for key in ['replay_passed', 'distinct_existing_spans',
          'display_P', 'display_uniform_budget_floor_cap', 'display_fixed_H_counting_coefficient_cap',
          'target_results']}, ensure_ascii=False))


if __name__ == '__main__':
    main()
