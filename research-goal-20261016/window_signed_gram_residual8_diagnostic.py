"""Finite saved-point SignedGram audit and one shared-edge dual payment.

No new point, optimizer, Lean, full-cover search or frozen-file edit.
All saved rational gradient samples, eight saved pressure vertices and
eight fixed prefix centres are checked against the original 45-pair cells.
One case-0 full-triangle dual is collected by edge before interval payment.
"""
from pathlib import Path
from fractions import Fraction as F
from math import sin, cos, pi, sqrt
import gzip
import hashlib
import json
import numpy as np
import window_phase_coefficients as intervals
from window_direct_gram_projection_probe import actual_phase

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SC = 32768
PARAM = ROOT/'research-20261016-followup/window_reweight_rational.json'
SAVED = HERE/'window_joint_cycle_projection_probe.json'
SAMPLES = HERE/'cover-gradient-mixture.json'
VERTICES = HERE/'cover-phase-psd-obstruction.json'
PARENTS = HERE/'cover-curvature-parent64.input.json.gz'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def evaluate(point, parameters, edges):
    positions = [F(0)]
    for gap in point:
        positions.append(positions[-1]+gap)
    xq = [positions[j]-positions[i] for i, j, a in edges]
    x = np.array(list(map(float, xq)))
    phase = [actual_phase(q) for q in xq]
    sn, cs = np.array([z[0] for z in phase]), np.array([z[1] for z in phase])
    theta = sqrt(2)/2
    Z = sin(theta)/theta
    A = cos(theta)*pi*x/(Z*(pi*pi*x*x-.5))
    B = 1/(1-2*pi*pi*x*x)
    d = np.array(parameters['window_coefficient_numerators_1e9'])/1e9
    modes = np.arange(1, 25)
    C = ((np.sinc(x[:, None]-modes)+np.sinc(x[:, None]+modes))@d)/(2*Z)
    u, v = A*sn, B*cs+C
    weights = np.array([float(a) for i, j, a in edges])
    Q, R, T = float(weights@(u*u)), float(weights@(v*v)), float(weights@(u*v))
    P = sum(F(b, 10**10)*q for b, q in zip(parameters['b_numerators'], point))
    zero = all(q.denominator == 1 for q in xq)
    if zero:
        assert Q == 0
        bound = float(P)+R
    else:
        assert Q > 0
        bound = float(P)+R-T*T/Q
    noninteger = next((e for e, q in enumerate(xq) if q.denominator != 1), None)
    return {'Q': Q, 'R': R, 'T': T, 'pressure_exact': str(P),
            'pressure_plus_Gram_lower_float': bound,
            'actual_F_float': float(P)+Q+2*T+R, 'Q_zero_exact_phase_case': zero,
            'positive_Q_noninteger_edge_witness': None if noninteger is None else {
                'edge': list(edges[noninteger][:2]), 'span_exact': str(xq[noninteger])}}, (A, cs, u+v, v/A)


def shared_edge_dual(case, state, data, edges):
    """One min-norm centre dual; uniform validity does not use numerical rank."""
    A, cs, k, beta = data
    lookup = {(i, j): e for e, (i, j, a) in enumerate(edges)}
    triangles, matrix, D = [], [], []
    for i in range(10):
        for j in range(i+1, 10):
            for l in range(j+1, 10):
                if all(pair in lookup for pair in [(i, j), (j, l), (i, l)]):
                    e, f, z = lookup[i, j], lookup[j, l], lookup[i, l]
                    row = np.zeros(41)
                    row[e], row[f], row[z] = cs[f]/A[e], cs[e]/A[f], -1/A[z]
                    matrix.append(row)
                    D.append(cs[f]*beta[e]+cs[e]*beta[f]-beta[z])
                    triangles.append((i, j, l, e, f, z))
    matrix, D = np.array(matrix), np.array(D)
    weights = np.array([float(a) for i, j, a in edges])
    left, singular, _ = np.linalg.svd(matrix/np.sqrt(weights), full_matrices=False)
    rank = int(sum(singular > singular[0]*1e-10))
    y_float = left[:, :rank]@((left[:, :rank].T@D)/(singular[:rank]**2))
    y = [F(round(float(v)*2**40), 2**40) for v in y_float]
    # H_e=A_e*(Cmat^T*y)_e. Collect rational constant and cosine coefficients
    # first, before touching any interval. Every repeated beta is paid once.
    constant = [F(0)]*41
    coefficients = [dict() for _ in edges]
    for (i, j, l, e, f, z), multiplier in zip(triangles, y):
        coefficients[e][f] = coefficients[e].get(f, F(0))+multiplier
        coefficients[f][e] = coefficients[f].get(e, F(0))+multiplier
        constant[z] -= multiplier
    packet_rows = case['uniform_cell_fixed_dual']['edge_packets']
    assert [row['pair'] for row in packet_rows] == [[i, j] for i, j, a in edges]
    all_pairs = [(i, i+1) for i in range(9)]+[(i, j) for i in range(10) for j in range(i+1, 10) if j-i != 1]
    all_lookup = {pair: e for e, pair in enumerate(all_pairs)}
    assert all(row['span_units'] == [state[0][all_lookup[i, j]], state[1][all_lookup[i, j]]]
               for row, (i, j, a) in zip(packet_rows, edges))
    def interval(key, e):
        return intervals.RI(*map(F, packet_rows[e][key]))
    cost_box_lower = F(0)
    independent_interval = intervals.RI(0)
    edge_records = []
    H_point = []
    for e, (i, j, a) in enumerate(edges):
        H = intervals.RI(constant[e])
        for f, coefficient in sorted(coefficients[e].items()):
            H += coefficient*interval('cosine', f)
        b, inverse_A = interval('beta', e), interval('inverse_A', e)
        assert inverse_A.l > 0 and a > 0
        raw = 2*H*b-(H*inverse_A).square()/a
        independent_interval += raw
        hlo, hhi = F(H.l, intervals.Q), F(H.u, intervals.Q)
        blo, bhi = F(b.l, intervals.Q), F(b.u, intervals.Q)
        rho = F(inverse_A.u, intervals.Q)**2/a
        # For fixed beta, 2*h*beta-rho*h^2 is concave in h; for fixed h
        # it is affine in beta. Thus the four corners give the box minimum.
        lower = min(2*h*bv-rho*h*h for h in [hlo, hhi] for bv in [blo, bhi])
        cost_box_lower += lower
        H_point.append(float(constant[e])+sum(float(c)*cs[f] for f, c in coefficients[e].items()))
        edge_records.append({'pair': [i, j], 'constant': str(constant[e]),
                             'cosine_coefficients': [[f, str(c)] for f, c in sorted(coefficients[e].items()) if c],
                             'H_interval': H.bounds(), 'beta_interval': b.bounds(),
                             'inverse_A_interval': inverse_A.bounds(),
                             'concave_box_lower': str(lower)})
    H_point = np.array(H_point)
    yp = np.array(list(map(float, y)))
    point_bound = float(sum(2*H_point*beta-(H_point/A)**2/weights))
    assert max(abs(H_point-A*(matrix.T@yp))) < 1e-11
    assert abs(float(2*yp@D)-float(sum(2*H_point*beta))) < 1e-11
    assert abs(point_bound-float(2*yp@D-(matrix.T@yp/weights)@(matrix.T@yp))) < 1e-10
    pressure_lower = sum(F(b, 10**10)*F(state[0][r], SC)
                         for r, b in enumerate(PARAMETERS['b_numerators']))
    return {'path': case['path'], 'triangles': [[i, j, l] for i, j, l, e, f, z in triangles],
            'rational_dual_denominator': str(2**40), 'rational_dual': list(map(str, y)),
            'centre_numerical_rank_hint': rank, 'centre_dual_E_lower_float': point_bound,
            'whole_cell_independent_interval': independent_interval.bounds(),
            'whole_cell_shared_edge_concave_E_lower': str(cost_box_lower),
            'whole_cell_shared_edge_concave_E_lower_float_summary': float(cost_box_lower),
            'pressure_lower_exact': str(pressure_lower),
            'whole_cell_F_lower_after_nonneg_E': str(pressure_lower+max(F(0), cost_box_lower)),
            'edge_records': edge_records, 'uniform_evidence_not_Lean': True,
            'one_new_centre_dual_only': True, 'LP_SDP_invoked': False}


PARAMETERS = json.loads(PARAM.read_bytes())


def main():
    saved = json.loads(SAVED.read_bytes())
    samples = json.loads(SAMPLES.read_bytes())
    vertices = json.loads(VERTICES.read_bytes())
    parents = json.loads(gzip.decompress(PARENTS.read_bytes()))
    cases = saved['residual8_point_diagnostics']
    for source in [PARAM, PARENTS, HERE/'window_phase_coefficients.py',
                   HERE/'window_interval_kernel.py', ROOT/'StructuralGoal20261016/WindowJetTableData.lean']:
        assert saved['source_sha256'][source.name] == sha(source)
    assert samples['receipt']['input_sha256'] == sha(PARENTS)
    states = {r['path']: r['before'] for r in parents['cases']}
    all_pairs = [(i, i+1) for i in range(9)]+[(i, j) for i in range(10) for j in range(i+1, 10) if j-i != 1]
    edges = [(i, j, F(a, 10**10)) for i, j, a in PARAMETERS['a_upper'] if a]
    pool = {r['path']: {} for r in cases}
    def insert(path, point, label):
        point = tuple(map(F, point))
        state = states[path]
        assert all(F(lo, SC) <= sum(point[i:j]) <= F(hi, SC)
                   for (i, j), lo, hi in zip(all_pairs, *state))
        pool[path].setdefault(point, []).append(label)
    for case in cases:
        insert(case['path'], case['gaps'], 'saved_prefix_centre')
    for row in samples['rows']:
        assert row['cell'] == states[row['path']]
        for n, point in enumerate(row['sample_points_gap_units']):
            insert(row['path'], [F(q)/SC for q in point], f'saved_gradient_sample_{n}')
    for row in vertices['rows']:
        insert(row['path'], [F(q)/SC for q in row['pressure_primal_gap_units']], 'saved_pressure_vertex')
    rows, counterexamples = [], []
    centre_data = None
    for case in cases:
        path = case['path']
        results = []
        for point, labels in pool[path].items():
            value, data = evaluate(point, PARAMETERS, edges)
            value.update({'gaps_exact': list(map(str, point)), 'saved_origins': labels})
            results.append(value)
            if value['pressure_plus_Gram_lower_float'] < .0088:
                counterexamples.append({'path': path, **value})
            if path == cases[0]['path'] and 'saved_prefix_centre' in labels:
                centre_data = data
        minimum = min(results, key=lambda r: r['pressure_plus_Gram_lower_float'])
        rows.append({'path': path, 'points_evaluated': len(results),
                     'minimum_saved_point_Gram_plus_pressure_float': minimum['pressure_plus_Gram_lower_float'],
                     'minimum_point_saved_origins': minimum['saved_origins'],
                     'all_exact_DBM_memberships_passed': True, 'points': results})
    assert not counterexamples, 'A low point requires a separate strict interval follow-up before final reporting.'
    assert centre_data is not None
    dual = shared_edge_dual(cases[0], states[cases[0]['path']], centre_data, edges)
    out = {'scope': __doc__, 'script_sha256': sha(Path(__file__)),
           'source_sha256': {p.name: sha(p) for p in [PARAM, SAVED, SAMPLES, VERTICES, PARENTS,
               HERE/'window_direct_gram_projection_probe.py', HERE/'window_phase_coefficients.py']},
           'threshold_exact': '11/1250', 'rows': rows,
           'existing_points_evaluated': sum(r['points_evaluated'] for r in rows),
           'exact_Q_zero_phase_points': sum(p['Q_zero_exact_phase_case'] for r in rows for p in r['points']),
           'minimum_positive_Q_float': min(p['Q'] for r in rows for p in r['points'] if p['Q'] > 0),
           'new_points_generated': 0, 'floating_low_counterexamples_found': len(counterexamples),
           'pointwise_strict_interval_counterexample_required': False,
           'case0_one_shared_edge_fixed_dual': dual,
           'whole_cell_exclusion_proven': False, 'global_floor_proven': False,
           'optimizer_Lean_fullcover_invoked': False}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out, indent=2)+'\n', encoding='utf8')
    print(json.dumps({'points': out['existing_points_evaluated'],
        'cases': [{k: r[k] for k in ['path', 'points_evaluated', 'minimum_saved_point_Gram_plus_pressure_float',
                                    'minimum_point_saved_origins']} for r in rows],
        'case0_centre_E_dual': dual['centre_dual_E_lower_float'],
        'case0_collected_concave_E_lower': dual['whole_cell_shared_edge_concave_E_lower_float_summary'],
        'case0_plain_collected_interval_E_lower': float(F(dual['whole_cell_independent_interval'][0]))}, indent=2))


if __name__ == '__main__':
    main()
