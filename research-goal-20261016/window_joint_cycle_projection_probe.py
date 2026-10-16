"""Small joint actual-phase cycle projection diagnostic.

No optimizer, Lean, cover search, or frozen-file edit is used. Pointwise
matrix solves are floating discovery; fixed rational duals are subsequently
evaluated with uniform rational intervals when requested by this script.
"""
from pathlib import Path
from fractions import Fraction as F
from math import pi, sin, cos, sqrt
import gzip
import hashlib
import json
from functools import lru_cache
import numpy as np
import window_interval_kernel as ik
import window_phase_coefficients as packets

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SC = 32768
PARAM = ROOT/'research-20261016-followup/window_reweight_rational.json'
PARAMS = json.loads(PARAM.read_bytes())
EDGES = [(i, j, F(a, 10**10)) for i, j, a in PARAMS['a_upper'] if a]
LOOK = {(i, j): e for e, (i, j, a) in enumerate(EDGES)}
ALL = [(i, i+1) for i in range(9)]+[(i, j) for i in range(10) for j in range(i+1, 10) if j-i != 1]
ALL_LOOK = {pair: i for i, pair in enumerate(ALL)}
PRESSURE = [F(v, 10**10) for v in PARAMS['b_numerators']]
STAR_ROOT = 1
STAR = {i: LOOK[tuple(sorted((i, STAR_ROOT)))] for i in range(10) if i != STAR_ROOT}
CHORDS = [e for e, (i, j, _) in enumerate(EDGES) if i != STAR_ROOT and j != STAR_ROOT]
assert len(STAR) == 9 and len(CHORDS) == 32


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sigma(i):
    assert i != STAR_ROOT
    return 1 if i > STAR_ROOT else -1


def point_data(gaps):
    g = np.array(list(map(float, gaps)))
    p = np.r_[0., np.cumsum(g)]
    x = np.array([p[j]-p[i] for i, j, _ in EDGES])
    theta = sqrt(2)/2
    z = sin(theta)/theta
    A = cos(theta)*pi*x/(z*(pi*pi*x*x-.5))
    B = 1/(1-2*pi*pi*x*x)
    f = np.r_[theta/pi, np.arange(1, 25)]
    d = np.r_[1., np.array(PARAMS['window_coefficient_numerators_1e9'])/1e9]
    k = ((np.sinc(x[:, None]-f)+np.sinc(x[:, None]+f)) @ d)/(2*z)
    cs = np.cos(pi*x)
    C = k-A*np.sin(pi*x)-B*cs
    beta = (B*cs+C)/A
    matrix = np.zeros((32, 41))
    rhs = np.zeros(32)
    for r, e in enumerate(CHORDS):
        i, j, _ = EDGES[e]
        ei, ej = STAR[i], STAR[j]
        matrix[r, e] = 1/A[e]
        matrix[r, ej] = -sigma(j)*cs[ei]/A[ej]
        matrix[r, ei] = sigma(i)*cs[ej]/A[ei]
        rhs[r] = beta[e]-sigma(j)*cs[ei]*beta[ej]+sigma(i)*cs[ej]*beta[ei]
    weights = np.array([float(a) for _, _, a in EDGES])
    gram = (matrix/weights) @ matrix.T
    y = np.linalg.solve(gram, rhs)
    projected = (matrix.T @ y)/weights
    bound = float(rhs @ y)
    E = float(weights @ (k*k))
    assert max(abs(matrix @ k-rhs)) < 1e-12
    assert abs(float(weights @ ((k-projected)**2))-(E-bound)) < 1e-12
    assert abs(float(rhs@y)-(2*rhs@y-y@gram@y)) < 1e-12
    single = rhs*rhs/np.diag(gram)
    all_triangles = []
    triangle_rhs = []
    for i in range(10):
        for j in range(i+1, 10):
            for l in range(j+1, 10):
                if all(pair in LOOK for pair in [(i, j), (j, l), (i, l)]):
                    e, f1, f2 = LOOK[i, j], LOOK[j, l], LOOK[i, l]
                    row = np.zeros(41)
                    row[e], row[f1], row[f2] = cs[f1]/A[e], cs[e]/A[f1], -1/A[f2]
                    all_triangles.append(row)
                    triangle_rhs.append(cs[f1]*beta[e]+cs[e]*beta[f1]-beta[f2])
    triangles = np.array(all_triangles)
    assert max(abs(triangles@k-triangle_rhs)) < 1e-12
    _, singular, vh = np.linalg.svd(triangles/np.sqrt(weights), full_matrices=False)
    rank = int(np.sum(singular > singular[0]*1e-10))
    full_projection = vh[:rank] @ (np.sqrt(weights)*k)
    full_bound = float(full_projection@full_projection)
    return {'gaps': list(map(str, gaps)), 'pressure': float(np.array(list(map(float, PRESSURE)))@g),
            'actual_E': E, 'actual_F': E+float(np.array(list(map(float, PRESSURE)))@g),
            'joint_cycle_E_lower_float': bound,
            'best_single_cycle_E_lower_float': float(max(single)),
            'sum_single_cycle_bounds_invalid_double_counts': float(sum(single)),
            'matrix_condition_float': float(np.linalg.cond(gram)),
            'maximum_identity_error_float': float(max(abs(matrix@k-rhs))),
            'rational_star_feasible_witness': {i: str(F(round(float(projected[e])*2**30), 2**30))
                                               for i, e in STAR.items()},
            'rational_dual_weights': [str(F(round(float(v)*2**30), 2**30)) for v in y],
            'projection_loss_float': E-bound,
            'all_positive_triangles': len(all_triangles),
            'all_triangle_numerical_rank': rank,
            'all_triangle_joint_E_lower_float': full_bound,
            'all_triangle_smallest_retained_singular_value_float': float(singular[rank-1]),
            'pointwise_only_not_uniform': True}


@lru_cache(None)
def sinpi_point(q):
    q = F(q)
    q -= 2*((q+1)//2)
    if q in [F(-1), F(0), F(1)]:
        return F(0), F(0)
    if q == F(1, 2):
        return F(1), F(1)
    if q == F(-1, 2):
        return F(-1), F(-1)
    interval = ik.interval.sin_interval(ik.PI*q)
    return max(F(-1), interval.l), min(F(1), interval.u)


def sinpi_range(lo, hi):
    lo, hi = F(lo), F(hi)
    assert lo <= hi
    if hi-lo >= 2:
        return packets.RI(-1, 1)
    a, b = sinpi_point(lo), sinpi_point(hi)
    lower, upper = min(a[0], b[0]), max(a[1], b[1])
    first = -((-(lo-F(1, 2))).numerator//(lo-F(1, 2)).denominator)
    last = (hi-F(1, 2)).numerator//(hi-F(1, 2)).denominator
    for n in range(first, last+1):
        if n % 2:
            lower = F(-1)
        else:
            upper = F(1)
    return packets.RI(lower, upper)


def amplitude_interval_point(x):
    px = ik.PI*x
    return ik.COSTH*px/(ik.Z*(px.square()-F(1, 2)))


def uniform_edges(state, provider):
    results = []
    h = ik.Z/(2*ik.PI*ik.COSTH)
    h = packets.RI(h.l, h.u)
    for i, j, _ in EDGES:
        index = ALL_LOOK[i, j]
        lo_units, hi_units = state[0][index], state[1][index]
        lo, hi = F(lo_units, SC), F(hi_units, SC)
        assert F(123, 128) <= lo <= hi <= 32
        cuts = [lo_units]+list(range((lo_units//1024+1)*1024, hi_units, 1024))+[hi_units]
        pieces = []
        digest = hashlib.sha256()
        for left, right in zip(cuts, cuts[1:]):
            _, _, amps = provider.amplitudes(F(left, SC), F(right, SC))
            ratio = amps[2]/amps[0]
            pieces.append(ratio)
            digest.update(json.dumps([left, right, ratio.ints()], separators=(',', ':')).encode())
        s0 = packets.hull(pieces)
        cosine = sinpi_range(lo+F(1, 2), hi+F(1, 2))
        invA = packets.RI(1/amplitude_interval_point(lo).u,
                         1/amplitude_interval_point(hi).l)
        beta = -h*cosine/packets.RI(lo, hi)+s0
        results.append({'inverse_A': invA, 'cosine': cosine, 'beta': beta,
                        'record': {'pair': [i, j], 'span_units': [lo_units, hi_units],
                                   'C_over_A': s0.bounds(), 'inverse_A': invA.bounds(),
                                   'cosine': cosine.bounds(), 'beta': beta.bounds(),
                                   'Taylor_piece_count': len(pieces),
                                   'Taylor_piece_endpoint_sha256': digest.hexdigest()}})
    return results


def uniform_dual(state, y_strings, provider):
    """The fixed rational dual E>=2*y.D-sum_e (C^T*y)_e^2/a_e."""
    rows = uniform_edges(state, provider)
    q = [packets.RI(0) for _ in EDGES]
    linear = packets.RI(0)
    for r, e in enumerate(CHORDS):
        i, j, _ = EDGES[e]
        ei, ej = STAR[i], STAR[j]
        y = F(y_strings[r])
        ri, rj, re = rows[ei], rows[ej], rows[e]
        D = re['beta']-sigma(j)*ri['cosine']*rj['beta']+sigma(i)*rj['cosine']*ri['beta']
        linear += 2*y*D
        q[e] += y*re['inverse_A']
        q[ej] -= y*sigma(j)*ri['cosine']*rj['inverse_A']
        q[ei] += y*sigma(i)*rj['cosine']*ri['inverse_A']
    cost = sum((v.square()/a for v, (_, _, a) in zip(q, EDGES)), packets.RI(0))
    bound = linear-cost
    pressure_lower = sum(b*F(state[0][ALL_LOOK[r, r+1]], SC) for r, b in enumerate(PRESSURE))
    rigorous_lower = F(bound.l, packets.Q)
    return {'fixed_rational_dual': list(y_strings),
            'twice_yD_interval': linear.bounds(), 'dual_quadratic_cost_interval': cost.bounds(),
            'uniform_E_dual_interval': bound.bounds(),
            'uniform_E_lower': str(rigorous_lower), 'pressure_lower': str(pressure_lower),
            'uniform_F_lower': str(pressure_lower+max(F(0), rigorous_lower)),
            'uniform_E_lower_float_summary': float(rigorous_lower),
            'uniform_F_lower_float_summary': float(pressure_lower+max(F(0), rigorous_lower)),
            'edge_packets': [row['record'] for row in rows],
            'uniform_interval_evidence_not_Lean': True}


def point_projection_witness(gaps, star_strings, provider):
    """Rational star coordinates plus exact chord formulas witness C*khat=D.

    An outward one-SC-unit microbox encloses each exact rational point span.
    It certifies an upper bound for this feasible projected-vector energy.
    The vector khat is not claimed to equal the actual kernel vector.
    """
    p = [F(0)]
    for gap in gaps:
        p.append(p[-1]+F(gap))
    span_units = [SC*(p[j]-p[i]) for i, j in ALL]
    state = [[v.numerator//v.denominator for v in span_units],
             [-((-v.numerator)//v.denominator) for v in span_units]]
    rows = uniform_edges(state, provider)
    khat = [None]*41
    for i, e in STAR.items():
        khat[e] = packets.RI(F(star_strings[i]))
    for e in CHORDS:
        i, j, _ = EDGES[e]
        ei, ej = STAR[i], STAR[j]
        ri, rj, re = rows[ei], rows[ej], rows[e]
        D = re['beta']-sigma(j)*ri['cosine']*rj['beta']+sigma(i)*rj['cosine']*ri['beta']
        khat[e] = (D+sigma(j)*ri['cosine']*rj['inverse_A']*khat[ej]
                   -sigma(i)*rj['cosine']*ri['inverse_A']*khat[ei])/re['inverse_A']
    energy = sum((a*v.square() for v, (_, _, a) in zip(khat, EDGES)), packets.RI(0))
    energy_upper = F(energy.u, packets.Q)
    pressure = sum(b*F(gap) for b, gap in zip(PRESSURE, gaps))
    return {'exact_point_positions': list(map(str, p)),
            'rational_star_coordinates': star_strings,
            'feasible_chord_formula': 'A_e*(D_e+sigma_j*cos(theta_i)*khat_star_j/A_star_j-sigma_i*cos(theta_j)*khat_star_i/A_star_i)',
            'selected_32_cycle_constraints_exactly_satisfied_by_construction': True,
            'point_pressure_exact': str(pressure),
            'projected_feasible_energy_upper': str(energy_upper),
            'pressure_plus_projection_upper': str(pressure+energy_upper),
            'pressure_plus_projection_upper_float_summary': float(pressure+energy_upper),
            'strictly_below_0088': pressure+energy_upper < F(11, 1250),
            'margin_to_0088': str(F(11, 1250)-pressure-energy_upper),
            'this_is_not_actual_kernel_energy_or_an_actual_sublevel_point': True}


def main():
    selection_path = HERE/'cover-lifted-graph-energy8.json'
    input_path = HERE/'cover-curvature-parent64.input.json.gz'
    selection = json.loads(selection_path.read_bytes())
    inputs = json.loads(gzip.decompress(input_path.read_bytes()))
    case_lookup = {row['path']: row for row in inputs['cases']}
    cases = []
    provider = packets.Provider()
    for row in selection['rows']:
        state = case_lookup[row['path']]['before']
        prefix = [F(0)]+[F(state[0][ALL_LOOK[0, j]]+state[1][ALL_LOOK[0, j]], 2*SC) for j in range(1, 10)]
        gaps = [prefix[i+1]-prefix[i] for i in range(9)]
        assert all(F(lo, SC) <= prefix[j]-prefix[i] <= F(hi, SC)
                   for (i, j), lo, hi in zip(ALL, *state))
        case = point_data(gaps)
        case['path'] = row['path']
        case['uniform_cell_fixed_dual'] = uniform_dual(state, case['rational_dual_weights'], provider)
        case['strict_point_projection_witness'] = point_projection_witness(gaps, case['rational_star_feasible_witness'], provider)
        cases.append(case)
    low_pressure = [point_data([F(1)]*9), point_data([F(9, 4)]+[F(1)]*8)]
    low_pressure_bands = []
    for radius_units in [256, 512, 1024]:
        state = [[(j-i)*SC-radius_units for i, j in ALL],
                 [(j-i)*SC+radius_units for i, j in ALL]]
        result = uniform_dual(state, low_pressure[0]['rational_dual_weights'], provider)
        result['radius'] = str(F(radius_units, SC))
        low_pressure_bands.append(result)
    assert F(low_pressure_bands[-1]['uniform_E_lower']) > F(4683, 10**6)
    assert F(low_pressure_bands[-1]['uniform_F_lower']) > F(8967, 10**6)
    out = {'scope': __doc__, 'script_sha256': sha(Path(__file__)),
           'source_sha256': {p.name: sha(p) for p in [PARAM, selection_path, input_path,
               HERE/'window_phase_coefficients.py', HERE/'window_interval_kernel.py',
               ROOT/'StructuralGoal20261016/WindowJetTableData.lean']},
           'star_root': STAR_ROOT, 'star_edge_indices': STAR,
           'independent_chord_edge_indices': CHORDS, 'cycles': 32,
           'residual8_point_diagnostics': cases,
           'low_pressure_point_diagnostics': low_pressure,
           'low_pressure_integer_bands': low_pressure_bands,
           'point_matrix_solves_floating': True, 'global_floor_proven': False,
           'optimizer_Lean_or_cover_invoked': False}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out, indent=2)+'\n', encoding='utf8')
    print(json.dumps({'residual8': [{key: row[key] for key in ['pressure', 'actual_E', 'joint_cycle_E_lower_float',
        'best_single_cycle_E_lower_float', 'matrix_condition_float', 'all_triangle_joint_E_lower_float',
        'all_triangle_numerical_rank']} | {
            'uniform_cell_E_lower': row['uniform_cell_fixed_dual']['uniform_E_lower_float_summary'],
            'projection_feasible_total_upper': row['strict_point_projection_witness']['pressure_plus_projection_upper_float_summary'],
            'projection_feasible_strict_below_0088': row['strict_point_projection_witness']['strictly_below_0088']}
        for row in cases], 'low_pressure_points': [{key: row[key] for key in ['pressure', 'actual_E',
        'joint_cycle_E_lower_float', 'best_single_cycle_E_lower_float']} for row in low_pressure],
        'low_pressure_bands': [{key: row[key] for key in ['radius', 'uniform_E_lower_float_summary',
        'uniform_F_lower_float_summary']} for row in low_pressure_bands]}, indent=2))


if __name__ == '__main__':
    main()
