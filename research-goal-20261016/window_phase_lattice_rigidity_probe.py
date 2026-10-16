"""Small actual-phase coercivity diagnostic; no optimizer, Lean, or cover job.

The accompanying note proves the graph inequality on paper. Rational interval
arithmetic certifies one counterexample to its being sufficient for localization.
Effective resistances are floating diagnostics only, not numerical certificates.
No frozen source or existing evidence is modified.
"""
from pathlib import Path
from fractions import Fraction as F
from math import isqrt, sin, pi, sqrt
import hashlib
import json
import numpy as np
import window_interval_kernel as ik
import window_phase_coefficients as phase_packets

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PARAM = ROOT / 'research-20261016-followup/window_reweight_rational.json'
I = ik.I


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def bounds(x):
    return [str(x.l), str(x.u)]


def sqrt_upper(x, digits=20):
    """Rational upward square root, checked with integer arithmetic."""
    x = F(x)
    scale = 10**digits
    n = isqrt(x.numerator * scale**2 // x.denominator)
    if F(n, scale)**2 < x:
        n += 1
    answer = F(n, scale)
    assert answer**2 >= x and (answer-F(1, scale))**2 < x
    return answer


def amplitude(x):
    px = ik.PI * x
    return ik.COSTH * px / (ik.Z * (px.square()-F(1, 2)))


def absolute_b(x):
    return I(1) / (2*(ik.PI*x).square()-1)


def cauchy_c_upper(left, coefficient_l2_squared):
    # Orthogonality: integral P(t)^2 dt = (sum d_m^2)/2.
    # integral cos(2*pi*x*t)^2 dt <= 1/2+1/(4*pi*left).
    cap2 = I(coefficient_l2_squared/2) * (F(1, 2)+I(1)/(4*ik.PI*left)) / ik.Z.square()
    return sqrt_upper(cap2.u)


def resistance_diagnostic(edges, conductances):
    lap = np.zeros((10, 10))
    for (i, j, _), h in zip(edges, conductances):
        lap[i, i] += h
        lap[j, j] += h
        lap[i, j] -= h
        lap[j, i] -= h
    inverse = np.linalg.inv(lap[:9, :9])
    output = []
    for i, j, _ in edges:
        v = np.zeros(9)
        if i < 9:
            v[i] += 1
        if j < 9:
            v[j] -= 1
        output.append(float(v @ inverse @ v))
    return {'effective_resistances_in_positive_edge_order': output,
            'maximum_effective_resistance': max(output),
            'radius_021_sufficient_energy_budget': sin(pi*.21)**2/max(output),
            'floating_not_certificate': True}


def signed_triangle_packet(edges):
    """Uniform rational interval evidence, not a new Lean consumer.

    x,y in [123/128,121/100], x+y <=221/100. Uniform C/A intervals
    come from the existing Taylor provider on an outward SC-grid cover.
    This costs only 18 one-dimensional packets; no optimization is used.
    """
    provider = phase_packets.Provider()
    domains = [(31488, 39650), (62976, 72418)]
    ratios = []
    packets = []
    for lo, hi in domains:
        intervals = []
        for left in range(lo, hi, 1024):
            right = min(left+1024, hi)
            n, radius, amps = provider.amplitudes(F(left, 32768), F(right, 32768))
            ratio = amps[2]/amps[0]
            intervals.append(ratio)
            packets.append({'lower_units': left, 'upper_units': right,
                            'integer_center': n, 'C_over_A_Q30': ratio.ints()})
        ratios.append(phase_packets.hull(intervals))
    short_lower = F(257, 10000)
    long_lower = F(-89, 1000)
    assert F(ratios[0].l, phase_packets.Q) >= short_lower
    assert F(ratios[1].l, phase_packets.Q) >= long_lower
    cosine = ik.interval.sin_interval(ik.PI/2+ik.PI*F(21, 100))
    cosine_lower = F(79, 100)
    assert cosine.l >= cosine_lower
    h = ik.Z/(2*ik.PI*ik.COSTH)
    frustration_lower = (h.l*(4*cosine_lower**2-1)/F(221, 100)
                         +2*short_lower*cosine_lower+long_lower)
    assert frustration_lower > F(2, 25)
    lookup = {(i, j): a for i, j, a in edges}
    a12, a23, a13 = lookup[1, 2], lookup[2, 3], lookup[1, 3]
    ashort = amplitude(F(121, 100)).l
    along = amplitude(F(221, 100)).l
    denominator_upper = 1/(a12*ashort**2)+1/(a23*ashort**2)+1/(a13*along**2)
    energy_lower = frustration_lower**2/denominator_upper
    assert energy_lower > F(1, 100000)
    return {'domain': {'x_y_lower': '123/128', 'x_y_upper': '121/100',
                       'x_plus_y_upper': '221/100'},
            'edges': [[1, 2], [2, 3], [1, 3]],
            'uniform_ratio_packets': packets,
            'uniform_C_over_A_short_hull': ratios[0].bounds(),
            'uniform_C_over_A_long_hull': ratios[1].bounds(),
            'rational_C_over_A_short_lower': str(short_lower),
            'rational_C_over_A_long_lower': str(long_lower),
            'cosine_radius_enclosure': bounds(cosine),
            'rational_cosine_lower': str(cosine_lower),
            'h_enclosure': bounds(h),
            'absolute_signed_frustration_lower': str(frustration_lower),
            'Cauchy_denominator_upper': str(denominator_upper),
            'triangle_weighted_kernel_energy_lower': str(energy_lower),
            'triangle_lower_exceeds_exact': '1/100000',
            'this_is_uniform_interval_evidence_not_Lean': True}


def main():
    parameters = json.loads(PARAM.read_bytes())
    edges = [(i, j, F(a, 10**10)) for i, j, a in parameters['a_upper'] if a]
    pressure = [F(b, 10**10) for b in parameters['b_numerators']]
    d = [F(v, 10**9) for v in parameters['window_coefficient_numerators_1e9']]
    assert d == ik.COEFF[1:] and len(edges) == 41
    sep = F(123, 128)
    c = F(11, 1250)
    excess = c-sep*sum(pressure)
    coefficient_l2_squared = sum(t*t for t in d)
    h, rows, residual_cap = [], [], I(0)
    conductance_sum = F(0)
    for i, j, weight in edges:
        lo = (j-i)*sep
        hi = lo+excess/min(pressure[i:j])
        amin = amplitude(hi)
        bcap = absolute_b(lo).u
        ccap = cauchy_c_upper(lo, coefficient_l2_squared)
        residual_cap += weight*(bcap+ccap)**2
        safe_conductance = weight*amin.l**2
        conductance_sum += safe_conductance
        h.append(float(safe_conductance))
        rows.append({'pair': [i, j], 'lower_span': str(lo), 'upper_span': str(hi),
                     'A_at_upper_enclosure': bounds(amin),
                     'B_absolute_upper': str(bcap), 'C_absolute_upper': str(ccap)})

    # A fully separated exact rank-one phase configuration outside every
    # integer-centred radius .21 basin: z_0=1; z_i=i for i=1,...,9.
    gaps = [F(9, 4)]+[F(1)]*8
    positions = [F(0)]
    for gap in gaps:
        positions.append(positions[-1]+gap)
    point_pressure = sum(b*g for b, g in zip(pressure, gaps))
    q_actual_amplitudes = I(0)
    q_frozen_root = I(0)
    for (i, j, weight), row in zip(edges, rows):
        if i == 0:
            # Span is an integer plus 1/4; its sin^2 is exactly 1/2.
            q_actual_amplitudes += weight*amplitude(positions[j]-positions[i]).square()/2
            q_frozen_root += weight*amplitude(F(row['upper_span'])).square()/2
    assert min(gaps) >= sep
    assert q_actual_amplitudes.u+point_pressure < c
    assert q_frozen_root.u <= q_actual_amplitudes.u
    human_q_bounds = [F(2801968097132, 10**15), F(2801968097134, 10**15)]
    assert human_q_bounds[0] <= q_actual_amplitudes.l <= q_actual_amplitudes.u <= human_q_bounds[1]
    # A cheap floating direct-kernel check is explicitly separated from the
    # exact counterexample, which concerns Q and never claims F<c.
    theta = sqrt(2)/2
    normalization = sin(theta)/theta
    frequencies = np.r_[theta/pi, np.arange(1, 25)]
    coefficients = np.r_[1., np.array([float(v) for v in d])]
    actual_kernel_energy = 0.
    for i, j, weight in edges:
        x = float(positions[j]-positions[i])
        kval = ((np.sinc(x-frequencies)+np.sinc(x+frequencies)) @ coefficients)/(2*normalization)
        actual_kernel_energy += float(weight)*kval*kval

    out = {
        'scope': __doc__, 'script_sha256': sha(Path(__file__)),
        'parameter_sha256': sha(PARAM),
        'interval_kernel_sha256': sha(HERE/'window_interval_kernel.py'),
        'phase_packet_provider_sha256': sha(HERE/'window_phase_coefficients.py'),
        'phase_packet_Taylor_data_sha256': sha(ROOT/'StructuralGoal20261016/WindowJetTableData.lean'),
        'floor_tested': str(c), 'separation': str(sep),
        'sum_pressure': str(sum(pressure)), 'root_excess_pressure': str(excess),
        'perturbation_coefficient_squared_sum': str(coefficient_l2_squared),
        'root_residual_squared_cap_enclosure': bounds(residual_cap),
        'root_safe_conductance_sum_exact': str(conductance_sum),
        'root_paid_graph_bound_vacuous_exact_check': residual_cap.u > conductance_sum,
        'root_phase_budget_diagnostic': (sqrt(float(excess))+sqrt(float(residual_cap.u)))**2,
        'root_zero_error_budget': float(excess),
        'root_graph_resistance_diagnostic': resistance_diagnostic(edges, h),
        'root_edges': rows,
        'signed_triangle_packet': signed_triangle_packet(edges),
        'rank_one_counterexample': {
            'gaps': list(map(str, gaps)), 'positions': list(map(str, positions)),
            'node_phases_e2piip': ['1']+['i']*9,
            'outside_every_integer_radius_021_basin': True,
            'distance_of_first_gap_to_integer': '1/4',
            'pressure_exact': str(point_pressure),
            'Q_actual_amplitudes_enclosure': bounds(q_actual_amplitudes),
            'Q_short_rational_enclosure': list(map(str, human_q_bounds)),
            'pressure_plus_Q_enclosure': bounds(q_actual_amplitudes+point_pressure),
            'positive_margin_below_0088': str(c-point_pressure-q_actual_amplitudes.u),
            'Q_root_frozen_amplitudes_enclosure': bounds(q_frozen_root),
            'actual_F_floating_diagnostic': float(point_pressure)+actual_kernel_energy,
            'this_is_not_an_actual_F_sublevel_counterexample': True},
        'global_localization_proven': False, 'new_global_floor_proven': False,
        'optimizer_or_Lean_invoked': False}
    output = Path(__file__).with_suffix('.json')
    output.write_text(json.dumps(out, indent=2)+'\n', encoding='utf8')
    print(json.dumps({
        'root_excess_pressure': float(excess),
        'root_residual_squared_cap': float(residual_cap.u),
        'root_phase_budget': out['root_phase_budget_diagnostic'],
        'root_max_effective_resistance': out['root_graph_resistance_diagnostic']['maximum_effective_resistance'],
        'radius_021_sufficient_energy_budget': out['root_graph_resistance_diagnostic']['radius_021_sufficient_energy_budget'],
        'counterexample_pressure_plus_Q': float(point_pressure+(q_actual_amplitudes.l+q_actual_amplitudes.u)/2),
        'counterexample_actual_F_diagnostic': out['rank_one_counterexample']['actual_F_floating_diagnostic'],
        'signed_triangle_frustration_lower': float(F(out['signed_triangle_packet']['absolute_signed_frustration_lower'])),
        'signed_triangle_energy_lower': float(F(out['signed_triangle_packet']['triangle_weighted_kernel_energy_lower'])),
        'counterexample_exact_Q_margin_positive': out['rank_one_counterexample']['positive_margin_below_0088']}, indent=2))


if __name__ == '__main__':
    main()
