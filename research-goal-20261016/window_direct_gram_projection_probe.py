"""Ten saved-point checks for the direct signed Gram projection formula.

This reads the frozen joint-cycle receipt and uses exactly its eight
residual midpoints plus two special low-pressure points. No new point,
matrix solve, optimizer, Lean, or cover search is used. Numerical results
are explicitly floating diagnostics; the identities are proved in the note.
"""
from pathlib import Path
from fractions import Fraction as F
from math import sin, cos, pi, sqrt
import hashlib
import json
import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SAVED = HERE/'window_joint_cycle_projection_probe.json'
PARAM = ROOT/'research-20261016-followup/window_reweight_rational.json'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def actual_phase(x):
    """Exact zero/parity decisions prevent fake Q>0 at integer phases."""
    if x.denominator == 1:
        return 0., (-1.)**int(x)
    if (2*x).denominator == 1:
        return (-1.)**int(x-F(1, 2)), 0.
    return sin(pi*float(x % 2)), cos(pi*float(x % 2))


def main():
    saved = json.loads(SAVED.read_bytes())
    parameters = json.loads(PARAM.read_bytes())
    edges = [(i, j, a/1e10) for i, j, a in parameters['a_upper'] if a]
    weights = np.array([a for i, j, a in edges])
    perturbations = np.array(parameters['window_coefficient_numerators_1e9'])/1e9
    modes = np.arange(1, 25)
    theta = sqrt(2)/2
    Z = sin(theta)/theta
    rows = []
    for index, source in enumerate(saved['residual8_point_diagnostics']+saved['low_pressure_point_diagnostics']):
        gaps = list(map(F, source['gaps']))
        positions = [F(0)]
        for gap in gaps:
            positions.append(positions[-1]+gap)
        spans_q = [positions[j]-positions[i] for i, j, a in edges]
        spans = np.array(list(map(float, spans_q)))
        phases = [actual_phase(x) for x in spans_q]
        sn = np.array([v[0] for v in phases])
        cs = np.array([v[1] for v in phases])
        A = cos(theta)*pi*spans/(Z*(pi*pi*spans*spans-.5))
        B = 1/(1-2*pi*pi*spans*spans)
        C = ((np.sinc(spans[:, None]-modes)+np.sinc(spans[:, None]+modes)) @ perturbations)/(2*Z)
        u = A*sn
        v = B*cs+C
        Q = float(weights@(u*u))
        R = float(weights@(v*v))
        T = float(weights@(u*v))
        E = float(weights@((u+v)**2))
        det = Q*R-T*T
        pair_sum = sum(weights[e]*weights[f]*(u[e]*v[f]-u[f]*v[e])**2
                       for e in range(41) for f in range(e+1, 41))
        integer_phases = all(x.denominator == 1 for x in spans_q)
        if integer_phases:
            assert Q == 0 and T == 0
            lower = R
            identity_error = abs(E-R)
        else:
            assert Q > 0
            lower = R-T*T/Q
            identity_error = abs(E-lower-(Q+T)**2/Q)
        assert abs(E-source['actual_E']) < 1e-12
        assert identity_error < 1e-12
        assert abs(det-pair_sum) < 1e-16
        full_cycle = source['all_triangle_joint_E_lower_float']
        star_cycle = source['joint_cycle_E_lower_float']
        if index < 8:
            assert abs(lower-full_cycle) < 1e-12
        else:
            assert lower > full_cycle+1e-3
        rows.append({'source_index': index, 'path': source.get('path'),
                     'gaps_exact': list(map(str, gaps)), 'Q': Q, 'R': R, 'T': T,
                     'actual_E': E, 'direct_projection_E_lower': lower,
                     'star_32_cycle_E_lower_saved': star_cycle,
                     'all_90_triangle_E_lower_saved': full_cycle,
                     'all_90_triangle_numerical_rank_saved': source['all_triangle_numerical_rank'],
                     'direct_minus_all_triangle': lower-full_cycle,
                     'direct_minus_star_32': lower-star_cycle,
                     'exact_integer_phase_case': integer_phases,
                     'projection_identity_absolute_error': identity_error,
                     'Gram_determinant': det, '820_pair_wedge_square_sum': float(pair_sum),
                     'Gram_determinant_pair_sum_absolute_error': abs(det-pair_sum),
                     'point_pressure_saved': source['pressure'],
                     'point_pressure_plus_direct_bound': source['pressure']+lower,
                     'division_free_sublevel_polynomial_at_c_0088': det-(.0088-source['pressure'])*Q,
                     'all_numbers_are_floating_diagnostics_except_exact_input_and_zero_decisions': True})
    output = {'scope': __doc__, 'script_sha256': sha(Path(__file__)),
              'source_sha256': {p.name: sha(p) for p in [SAVED, PARAM]},
              'rows': rows,
              'maximum_generic_8_direct_vs_full_cycle_difference': max(abs(r['direct_minus_all_triangle']) for r in rows[:8]),
              'maximum_projection_identity_absolute_error': max(r['projection_identity_absolute_error'] for r in rows),
              'maximum_Gram_determinant_pair_sum_absolute_error': max(r['Gram_determinant_pair_sum_absolute_error'] for r in rows),
              'new_points_evaluated': 0, 'matrix_solves_invoked': 0,
              'optimizer_Lean_cover_invoked': False, 'uniform_cell_certificate_produced': False,
              'global_floor_or_zero_proportion_proven': False}
    Path(__file__).with_suffix('.json').write_text(json.dumps(output, indent=2)+'\n', encoding='utf8')
    print(json.dumps({'generic8_max_difference': output['maximum_generic_8_direct_vs_full_cycle_difference'],
                      'max_projection_identity_error': output['maximum_projection_identity_absolute_error'],
                      'max_Gram_pair_identity_error': output['maximum_Gram_determinant_pair_sum_absolute_error'],
                      'rows': [{key: r[key] for key in ['source_index', 'Q', 'direct_projection_E_lower',
                          'all_90_triangle_E_lower_saved', 'all_90_triangle_numerical_rank_saved',
                          'direct_minus_all_triangle']} for r in rows]}, indent=2))


if __name__ == '__main__':
    main()
