"""Small identity diagnostic for a possible future two-layer phase method.

This does not prove a uniform coefficient bound, a PSD certificate, a global
energy floor, or a zero proportion. It neither runs Lean nor modifies proofs.
Existing rational interval routines are used only as a diagnostic oracle.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib
import json
import re
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))
import window_interval_kernel as ik

I, PI, THETA, Z = ik.I, ik.PI, ik.THETA, ik.Z


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def contains_zero(x):
    return x.l <= 0 <= x.u


def abs_upper(x):
    return max(abs(x.l), abs(x.u))


def regular_amplitudes(x, n):
    """C + A sin(pi*x) + B cos(pi*x), with the mode n isolated."""
    x = F(x)
    px = PI*x
    numerator = ik.COSTH*px/(px.square()-THETA.square())
    for m in range(1, 25):
        if m != n:
            numerator += I(ik.COEFF[m]*((-1)**m)*x)/(PI*(x*x-m*m))
    a = numerator/Z
    b = I(1)/(1-2*px.square())
    if n <= 24:
        delta = x-n
        z = PI*delta
        sinc = ik.sinc_jet(z, ik.interval.sin_interval(z),
                          ik.interval.sin_interval(PI/2+z), 0)[0]
        c = (ik.COEFF[n]*x*sinc)/(Z*(x+n))
    else:
        c = I(0)
    return a, b, c


def all_mode_amplitudes(x, n=None):
    """All shifted-sinc pairs in C; no positive integer poles in A or B."""
    x = F(x)
    px = PI*x
    a = ik.COSTH*px/(Z*(px.square()-THETA.square()))
    b = I(1)/(1-2*px.square())
    cs, sn = phase(x)
    c = I(0)
    for m in range(1, 25):
        sinc = ik.sinc_jet(PI*(x-m), ((-1)**m)*sn,
                          ((-1)**m)*cs, 0)[0]
        c += (ik.COEFF[m]*x*sinc)/(Z*(x+m))
    return a, b, c


def phase(x):
    return (ik.interval.sin_interval(PI/2+PI*x),
            ik.interval.sin_interval(PI*x))


def conjugate_product(x, y):
    # Real and imaginary parts of conjugate(x)*y.
    return x[0]*y[0]+x[1]*y[1], x[0]*y[1]-x[1]*y[0]


def doubled(x):
    return x[0].square()-x[1].square(), 2*x[0]*x[1]


def main():
    window_source = ROOT/'StructuralW10Followup20261016/NewWindows.lean'
    source_block = window_source.read_text(encoding='utf8').split('def nums24')[1]
    nums = [int(v) for _, v in re.findall(r'\|\s*(\d+)\s*=>\s*(-?\d+)', source_block)]
    assert len(nums) == 24
    assert ik.COEFF[1:] == [F(v, 10**9) for v in nums]
    rows = []
    for n in [1, 2, 3, 9, 12, 16, 24, 32]:
        for delta in [F(-1, 5), F(-1, 10**12), F(0), F(1, 10**12), F(1, 5)]:
            x = n+delta
            a, b, c = regular_amplitudes(x, n)
            cs, sn = phase(x)
            actual_k = ik.kernel_jet(x, 0)[0]
            reconstructed = c+a*sn+b*cs
            q0 = c.square()+(a.square()+b.square())/2
            q1r, q1i = 2*c*b, -2*c*a
            q2r, q2i = (b.square()-a.square())/2, -a*b
            cs2, sn2 = doubled((cs, sn))
            harmonic = q0+q1r*cs-q1i*sn+q2r*cs2-q2i*sn2
            err_k = reconstructed-actual_k
            err_w = harmonic-actual_k.square()
            assert contains_zero(err_k) and contains_zero(err_w)
            aa, bb, cc = all_mode_amplitudes(x)
            global_k = cc+aa*sn+bb*cs
            global_harmonic = (cc.square()+(aa.square()+bb.square())/2
                +2*cc*bb*cs+2*cc*aa*sn
                +(bb.square()-aa.square())*cs2/2+aa*bb*sn2)
            global_err_k = global_k-actual_k
            global_err_w = global_harmonic-actual_k.square()
            assert contains_zero(global_err_k) and contains_zero(global_err_w)
            rows.append({'n': n, 'delta': str(delta),
                         'k_difference_enclosure': [str(err_k.l), str(err_k.u)],
                         'w_difference_enclosure': [str(err_w.l), str(err_w.u)],
                         'global_k_difference_enclosure': [str(global_err_k.l), str(global_err_k.u)],
                         'global_w_difference_enclosure': [str(global_err_w.l), str(global_err_w.u)]})

    # One ten-node configuration, using all 41 positive actual ledger edges.
    # This evaluates the matrices at that configuration; it does not freeze
    # the amplitudes on a surrounding cell or certify any PSD inequality.
    ledger_source = ROOT/'StructuralW10Followup20261016/NewLedger.lean'
    ledger_text = ledger_source.read_text(encoding='utf8')
    edge_block = ledger_text.split('def aN')[1].split('def bN')[0]
    edges = [(int(i), int(j), F(int(v), 10**10)) for i, j, v in
             re.findall(r'\|\s*(\d+),\s*(\d+)\s*=>\s*(\d+)', edge_block)
             if int(v) > 0]
    assert len(edges) == 41
    p = [F(i)+F(i*i, 1000) for i in range(10)]
    u = [phase(x) for x in p]
    v = [doubled(z) for z in u]
    matrix_rows = []
    for name, amplitudes in [('local_resonance', regular_amplitudes),
                             ('all_modes_in_C', all_mode_amplitudes)]:
        pair_energy, constant, layer1, layer2 = (I(0) for _ in range(4))
        for i, j, weight in edges:
            x = p[j]-p[i]
            a, b, c = amplitudes(x, j-i)
            q0 = c.square()+(a.square()+b.square())/2
            q1r, q1i = 2*c*b, -2*c*a
            q2r, q2i = (b.square()-a.square())/2, -a*b
            ur, ui = conjugate_product(u[i], u[j])
            vr, vi = conjugate_product(v[i], v[j])
            pair_energy += weight*ik.kernel_jet(x, 0)[0].square()
            constant += weight*q0
            layer1 += 2*(weight/2)*(q1r*ur-q1i*ui)
            layer2 += 2*(weight/2)*(q2r*vr-q2i*vi)
        matrix_difference = constant+layer1+layer2-pair_energy
        assert contains_zero(matrix_difference)
        assert abs_upper(matrix_difference) < F(1, 10**18)
        matrix_rows.append({'representation': name,
            'difference_enclosure': list(map(str, [matrix_difference.l, matrix_difference.u])),
            'difference_abs_upper_float': float(abs_upper(matrix_difference))})
    max_k = max(max(abs(F(r['k_difference_enclosure'][0])),
                    abs(F(r['k_difference_enclosure'][1]))) for r in rows)
    max_w = max(max(abs(F(r['w_difference_enclosure'][0])),
                    abs(F(r['w_difference_enclosure'][1]))) for r in rows)
    max_global_k = max(max(abs(F(v)) for v in r['global_k_difference_enclosure']) for r in rows)
    max_global_w = max(max(abs(F(v)) for v in r['global_w_difference_enclosure']) for r in rows)
    assert max_k < F(1, 10**18) and max_w < F(1, 10**18), (float(max_k), float(max_w))
    assert max_global_k < F(1, 10**18) and max_global_w < F(1, 10**18)
    inputs = [window_source, ledger_source,
              ROOT/'StructuralGoal20261016/WindowKernel.lean',
              ROOT/'StructuralGoal20261016/WindowGramExpansion.lean',
              ROOT/'formal/upstream/ajp88-reweighted-nine-point.lean',
              HERE/'window_interval_kernel.py',
              ROOT/'research-20261016-followup/global_periodic_upper_bound.py',
              ROOT/'research-20261016-followup/window_reweight_rational.json']
    doc = {
        'status': 'Identity diagnostics only; no uniform or PSD proof.',
        'source_coefficients_match': True,
        'point_cases': len(rows), 'all_difference_enclosures_contain_zero': True,
        'max_k_difference_abs_upper': str(max_k),
        'max_w_difference_abs_upper': str(max_w),
        'max_global_k_difference_abs_upper': str(max_global_k),
        'max_global_w_difference_abs_upper': str(max_global_w),
        'point_rows': rows,
        'matrix_diagnostic': {
            'node_positions': list(map(str, p)), 'positive_edges': len(edges),
            'actual_pair_energy_interval': list(map(str, [pair_energy.l, pair_energy.u])),
            'representations': matrix_rows,
            'factor_of_two_in_offdiagonal': 'H_ij = weight_ij*q_ij/2',
            'amplitudes_evaluated_at_same_point': True,
            'uniform_coefficient_payments_proven': False,
            'PSD_dual_generated_or_proven': False},
        'lean_verified': False,
        'complete_global_cover': False,
        'new_zero_proportion_proven': False,
        'inputs': [{'path': str(p.relative_to(ROOT)).replace('\\', '/'),
                    'sha256': digest(p)} for p in inputs],
        'diagnostic_script_sha256': digest(Path(__file__))}
    target = HERE/'window_phase_hermitian_diagnostic.json'
    target.write_text(json.dumps(doc, indent=2)+'\n', encoding='utf8')
    print(json.dumps({'point_cases': len(rows), 'all_identities_consistent': True,
                      'max_k_error': float(max_k), 'max_w_error': float(max_w),
                      'max_global_k_error': float(max_global_k),
                      'max_global_w_error': float(max_global_w),
                      'matrix_diagnostics': matrix_rows,
                      'diagnostic_only': True, 'output': str(target)}))


if __name__ == '__main__':
    main()
