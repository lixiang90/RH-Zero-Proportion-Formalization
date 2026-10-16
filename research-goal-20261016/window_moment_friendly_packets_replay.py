"""Independent stdlib preflight of Lean-friendly scalar moment packets.

Read normalized Q30 W only after comparing it with BOTH Lean raw and
rational-table literals. Recompute rational-scale point Horner, all V/T/eps
thresholds, fixed-corner q2 Horner masks, coarse intervals and old-table
reuse indices. Rebuild the broadened energy-zero row and independently
aggregate the original positive integer weights. No Lean/optimizer runs;
the old integer rows are bound to the previous complete independent replay.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import hashlib
import json
import re
import sys
import time

import cover_curvature_actual_feed as feed

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
FS, SC, PD, GD, DS, VCOUNT = 10**30, 32768, 10**7, 10**6, 10**15, 464
M24 = F(44, 7)**24
PAIRS = [(s, r) for s in range(9) for r in range(s, 9)]
HI = {pair: 50+k for k, pair in enumerate(PAIRS)}
ALL = [(i, i+1) for i in range(9)]+[(i, j) for i in range(9) for j in range(i+2, 10)]
LOOK = {p: i for i, p in enumerate(ALL)}
sha = lambda raw: hashlib.sha256(raw).hexdigest()
floor = lambda x: x.numerator//x.denominator
ceil = lambda x: -((-x.numerator)//x.denominator)


def coefficients(W, n, q):
    return [tuple(value*(factorial(j+q)//factorial(j)) for value in W[n][j+q])
            for j in range(24-q)]


def fixed_horner(W, n, q, l, u):
    assert 1 <= n <= 32 and -F(1, 2) <= l-n <= u-n <= F(1, 2)
    X = floor((l-n)*FS), ceil((u-n)*FS)
    cs = coefficients(W, n, q)
    value = cs[-1]
    mask = 0
    for j in range(len(cs)-2, -1, -1):
        products = [value[a]*X[b] for a, b in [(0, 0), (0, 1), (1, 0), (1, 1)]]
        low = min(range(4), key=products.__getitem__)
        high = max(range(4), key=products.__getitem__)
        mask += (low+4*high)*16**j
        assert all(products[low] <= p <= products[high] for p in products)
        value = cs[j][0]+products[low]//FS, cs[j][1]-((-products[high])//FS)
    return value, mask


def rational_scale_horner(W, n, q, p):
    """Exactly WindowFixedPolynomial.poly/scale with rational delta p-n."""
    cs = coefficients(W, n, q)
    value = cs[-1]
    delta = p-n
    for c in reversed(cs[:-1]):
        a, b = value if delta >= 0 else value[::-1]
        value = c[0]+floor(a*delta), c[1]+ceil(b*delta)
    return value


def broadened_energy(state, centre, terms, bs, point_rows, point_indices, lowers):
    lo, hi = [[F(x, SC) for x in row[:9]] for row in state]
    mid = [(a+b)/2 for a, b in zip(lo, hi)]
    rad = [(b-a)/2 for a, b in zip(lo, hi)]
    assert all(r > 0 for r in rad)
    f_lower = sum(F(b, 10**10)*p for b, p in zip(bs, centre))
    gm, ge = [F(b, 10**10) for b in bs], [F(0)]*9
    for (i, j, aw), index in zip(terms, point_indices):
        point = point_rows[index]
        assert F(point['p']) == sum(centre[i:j])
        a = F(aw, 10**10)
        f_lower += a*F(point['value_lower'])
        for r in range(i, j):
            gm[r] += a*F(point['slope'])
            ge[r] += a*F(point['slope_error'])
    payment = sum(e*max(abs(a-c), abs(b-c)) for e, a, b, c in zip(ge, lo, hi, centre))
    # Construct the physical-coordinate linear part directly. Only the
    # Taylor quadratic's squared delta is expressed in y/H coordinates.
    row = {r: gm[r] for r in range(9)}
    constant = f_lower-payment-sum(v*p for v, p in zip(gm, centre))
    for (i, j, aw), L in zip(terms, lowers):
        weight = F(aw, 10**10)*L/2
        delta = sum(mid[i:j])-sum(centre[i:j])
        constant += weight*delta**2
        for r in range(i, j):
            row[r] += 2*weight*delta
            constant -= 2*weight*delta*mid[r]
            for s in range(r, j):
                k = HI[r, s]
                row[k] = row.get(k, F(0))+(1 if r == s else 2)*weight*rad[r]*rad[s]
    return {i: a for i, a in row.items() if a}, F(11, 1250)-constant, {
        'F_lower': f_lower, 'gradient_midpoint': gm, 'gradient_error': ge,
        'uniform_gradient_error_payment': payment, 'quadratic_constant': constant}


def main():
    started = time.monotonic()
    input_raw = (HERE/'window-moment-friendly-packets.json').read_bytes()
    document = json.loads(input_raw)
    strict_raw = (HERE/'cover-cross-moment-integer-two.json').read_bytes()
    strict = json.loads(strict_raw)
    previous_raw = (HERE/'cover-cross-moment-independent-replay.json').read_bytes()
    previous = json.loads(previous_raw)
    assert previous['all_checks_passed'] and previous['input_sha256'] == sha(strict_raw)
    norm_raw = (HERE/'window_normalized_interval.json').read_bytes()
    params_raw = (ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes()
    current_raw = (HERE/'cover-curvature-actual-active.json').read_bytes()
    for key, raw in [('strict_original', strict_raw), ('normalized_W', norm_raw),
                     ('existing_curvature_grid', current_raw), ('parameters', params_raw)]:
        assert document['inputs_sha256'][key] == sha(raw)
    producer_raw = (HERE/'window_moment_friendly_packets.py').read_bytes()
    assert document['script_sha256'] == sha(producer_raw)
    W, _ = feed.load()
    raw_lean = (ROOT/'StructuralGoal20261016/WindowRawCoefficientData.lean').read_bytes()
    jet_lean = (ROOT/'StructuralGoal20261016/WindowJetTableData.lean').read_bytes()
    block = jet_lean.decode('utf8').split('def wValues :', 1)[1].split('\ndef ', 1)[0]
    jet_literals = [(int(l), int(u)) for l, u in re.findall(r'qi30\s*\((-?\d+)\)\s*\((-?\d+)\)', block)]
    assert len(jet_literals) == 33*24
    assert jet_literals[24:] == [pair for n in range(1, 33) for pair in W[n]]
    point_witnesses = []
    for index, row in enumerate(document['point_rows']):
        n, p = row['n'], F(row['p'])
        assert n == round(p) and ((p-n)*FS).denominator == 1
        witness = {'point_index': index, 'n': n, 'p': str(p), 'jets': []}
        for q in [0, 1]:
            poly, mask = fixed_horner(W, n, q, p, p)
            scalar_poly = rational_scale_horner(W, n, q, p)
            assert poly == scalar_poly
            rem = M24*abs(p-n)**(24-q)/factorial(24-q)
            L, U = F(poly[0], FS)-rem, F(poly[1], FS)+rem
            if q == 0:
                value = F(row['value_lower'])
                assert value == F(floor(L*PD)-1, PD)
                assert (value+rem)*FS <= poly[0]
                margins = [F(poly[0], FS)-value-rem]
            else:
                T, eps = F(row['slope']), F(row['slope_error'])
                assert T == F(round(F(poly[0]+poly[1], FS)*PD/2), PD)
                assert eps == F(ceil(max(abs(L-T), abs(U-T))*PD)+1, PD)
                assert (T-eps+rem)*FS <= poly[0] and poly[1] <= (T+eps-rem)*FS
                margins = [F(poly[0], FS)-(T-eps+rem), T+eps-rem-F(poly[1], FS)]
            assert min(margins) > 0
            witness['jets'].append({'q': q, 'degree': 23-q, 'fixed_poly_endpoints': list(map(str, poly)),
                                    'corner_mask': str(mask), 'Taylor_remainder': str(rem),
                                    'actual_fixed_point_check_margins': list(map(str, margins)),
                                    'rational_scale_equals_fixed_corner_point': True})
        point_witnesses.append(witness)
    current = json.loads(current_raw)['grid_rows']
    lean_grid_raw = (ROOT/'StructuralGoal20261016/WindowCurvatureGridData.lean').read_bytes()
    pattern = r'⟨(\d+),(true|false),(\d+),\((-?\d+)\),\((-?\d+)\),(true|false),(\d+),\((-?\d+)\)⟩'
    literals = re.findall(pattern, lean_grid_raw.decode('utf8'))
    assert len(literals) == len(current) == 331
    for row, literal in zip(current, literals):
        k, has2, m2, L, U, has4, m4, B = literal
        assert int(k) == row['k'] and (has2 == 'true') == ('q2' in row) and (has4 == 'true') == ('q4' in row)
        assert list(map(int, [m2, L, U])) == row.get('q2', [0, 0, 0])
        assert list(map(int, [m4, B])) == row.get('q4', [0, 0])
    existing = {r['k']: (i, r['q2']) for i, r in enumerate(current) if 'q2' in r}
    old_all = {r['k'] for r in current}
    new_rows = {r['k']: r for r in document['new_q2_rows']}
    grid_witnesses, grid_bounds = [], {}
    remainder2 = M24*F(1, 2)**22/factorial(22)
    for k in document['all_q2_cells']:
        l, u = F(k, 64), F(k+1, 64)
        n = (k+32)//64
        assert n == round((l+u)/2)
        poly, mask = fixed_horner(W, n, 2, l, u)
        L = F(floor((F(poly[0], FS)-remainder2)*GD)-1, GD)
        U = F(ceil((F(poly[1], FS)+remainder2)*GD)+1, GD)
        assert (L+remainder2)*FS <= poly[0] and poly[1] <= (U-remainder2)*FS
        grid_bounds[k] = L, U
        if k in existing:
            old_index, (oldmask, oldL, oldU) = existing[k]
            assert L <= F(oldL, DS) <= F(oldU, DS) <= U and k not in new_rows
        else:
            row = new_rows[k]
            assert row['n'] == n and int(row['mask']) == mask and F(row['lower']) == L and F(row['upper']) == U
            assert not row['reuse_current_q2'] and row['current_index'] is None
            old_index = None
        assert (L*DS).denominator == (U*DS).denominator == 1
        grid_witnesses.append({'k': k, 'n': n, 'mask': str(mask), 'fixed_poly_endpoints': list(map(str, poly)),
                               'Taylor_remainder': str(remainder2), 'lower_DS_integer': str(int(L*DS)),
                               'upper_DS_integer': str(int(U*DS)), 'reuse_q2_index_in_old331': old_index})
    assert len(new_rows) == len(set(grid_bounds)-set(existing))
    params = json.loads(params_raw)
    terms = [tuple(t) for t in params['a_upper'] if t[2]]
    old_cases = {r['path']: r for r in strict['rows']}
    results, required_cells = [], set()
    for case in document['rows']:
        old = old_cases[case['path']]
        state, packet = old['cell'], case['energy0']
        centre = list(map(F, packet['centre']))
        assert centre == list(map(F, old['energy_packets'][0]['centre']))
        assert all(F(l, SC) <= sum(centre[i:j]) <= F(u, SC) for (i, j), l, u in zip(ALL, *state))
        lowers = []
        for (i, j, aw), recorded_range in zip(terms, packet['grid_ranges']):
            z = LOOK[i, j]
            first, last = state[0][z]//512, (max(state[0][z]+1, state[1][z])+511)//512-1
            assert recorded_range == [first, last]
            required_cells.update(range(first, last+1))
            lowers.append(min(grid_bounds[k][0] for k in range(first, last+1)))
        assert lowers == list(map(F, packet['whole_span_second_lower']))
        coeff, bound, fields = broadened_energy(state, centre, terms, params['b_numerators'], document['point_rows'], packet['point_indices'], lowers)
        assert sorted(coeff.items()) == [(i, F(v)) for i, v in packet['row']] and bound == F(packet['bound'])
        for key, value in fields.items():
            assert value == (list(map(F, packet[key])) if isinstance(value, list) else F(packet[key]))
        bounds = [tuple(map(F, b)) for b in old['box_bounds']]
        N = int(old['integerization_denominator'])
        rounded = {i: round(a*N) for i, a in coeff.items()}
        error = sum(abs(a-F(rounded[i], N))*max(abs(bounds[i][0]), abs(bounds[i][1])) for i, a in coeff.items())
        B = ceil(N*(bound+error))
        replacement = case['replacement_integer_row']
        assert {i: a for i, a in rounded.items() if a} == {int(i): int(a) for i, a in replacement['coeff'].items()}
        assert B == int(replacement['bound']) and error == F(replacement['rounding_payment'])
        total, totalB, mu_sum, energies = {}, 0, 0, 0
        for selected in old['selected_integer_rows']:
            mu = int(selected['weight'])
            assert mu > 0
            mu_sum += mu
            if selected['meta'] == ['energy', 0]:
                a, rhs = rounded, B
                energies += 1
            else:
                assert selected['meta'] != ['energy', 1]
                a, rhs = {i: int(v) for i, v in selected['integer_coefficients']}, int(selected['integer_bound'])
            totalB += mu*rhs
            for i, value in a.items(): total[i] = total.get(i, 0)+mu*value
        total = {i: a for i, a in total.items() if a}
        minimum = sum(a*bounds[i][0 if a >= 0 else 1] for i, a in total.items())
        margin = minimum-totalB
        aggregate = case['aggregate']
        assert energies == 1 and margin > 0 and case['preserved_dual_weights'] and aggregate['strict_exclusion']
        assert total == {int(i): int(v) for i, v in aggregate['coefficient'].items()}
        assert totalB == int(aggregate['bound']) and minimum == F(aggregate['box_minimum'])
        assert margin == F(aggregate['strict_margin']) and margin/(N*mu_sum) == F(case['normalized_strict_margin'])
        results.append({'path': case['path'], 'all_checks_passed': True, 'scalar_points_consumed': 41,
                        'preserved_positive_weights': len(old['selected_integer_rows']), 'energy_rows_replaced': 1,
                        'strict_margin': str(margin), 'normalized_strict_margin': str(margin/(N*mu_sum)),
                        'actual_Lean_exclusion_proven': False})
    assert required_cells == set(document['all_q2_cells'])
    plan = document['plan']
    counts = {'point_rows': len(point_witnesses), 'required_q2_cells': len(grid_bounds),
              'reused_q2_cells': len(set(grid_bounds)&set(existing)), 'new_q2_cells': len(new_rows),
              'overlap_with_old331_all_rows': len(set(grid_bounds)&old_all),
              'not_present_in_old331_any_flag': len(set(grid_bounds)-old_all), 'new_q4_cells': 0}
    assert all(plan[k] == value for k, value in counts.items() if k in plan)
    assert not any(name in sys.modules for name in ['numpy', 'scipy', 'networkx'])
    sources = [Path(__file__), HERE/'window_moment_friendly_packets.py', HERE/'cover_curvature_actual_feed.py',
               HERE/'cover_cross_moment_exact_rows.py', ROOT/'StructuralGoal20261016/WindowRawCoefficientData.lean',
               ROOT/'StructuralGoal20261016/WindowJetTableData.lean', ROOT/'StructuralGoal20261016/WindowFixedPoint.lean',
               ROOT/'StructuralGoal20261016/WindowFixedPolynomial.lean', ROOT/'StructuralGoal20261016/WindowCellDerivative.lean',
               ROOT/'StructuralGoal20261016/WindowFixedHornerChoice.lean', ROOT/'StructuralGoal20261016/WindowCurvatureGridData.lean']
    out = {'scope': __doc__, 'script_sha256': sha(Path(__file__).read_bytes()), 'input_sha256': sha(input_raw),
           'strict_original_sha256': sha(strict_raw), 'previous_complete_independent_replay_sha256': sha(previous_raw),
           'normalized_W_sha256': sha(norm_raw), 'existing_grid_sha256': sha(current_raw),
           'parameters_sha256': sha(params_raw), 'sources_sha256': {p.relative_to(ROOT).as_posix(): sha(p.read_bytes()) for p in sources},
           'all_checks_passed': True, 'no_site_packages': sys.flags.no_site, 'counts': counts,
           'raw_and_rational_Lean_W_literals_equal': True, 'point_denominator': PD, 'grid_denominator': GD,
           'point_witnesses': point_witnesses, 'q2_grid_witnesses': grid_witnesses, 'cases': results,
           'actual_point_fixed_checks_preflight': True, 'actual_q2_cell_checks_preflight': True,
           'ordinary_Lean_run_by_this_replay': False, 'actual_Lean_exclusions': 0,
           'complete_global_cover': False, 'new_zero_proportion_proven': False, 'seconds': time.monotonic()-started}
    output = HERE/'window-moment-friendly-independent-replay.json'
    output.write_text(json.dumps(out, separators=(',', ':'))+'\n', encoding='utf8')
    print(json.dumps({'all_checks_passed': True, 'counts': counts,
                      'normalized_margins': [float(F(c['normalized_strict_margin'])) for c in results],
                      'seconds': out['seconds'], 'receipt_sha256': sha(output.read_bytes())}), flush=True)


if __name__ == '__main__':
    main()
