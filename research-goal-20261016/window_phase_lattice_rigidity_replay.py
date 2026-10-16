"""Independent exact checks of the phase-localization obstruction and cycle packet.

No producer import, NumPy, optimizer, Lean, or cover search is used. The
existing rational interval kernel and phase Taylor provider are shared and
explicitly hashed; this does not independently reprove their analytic bounds.
"""
from pathlib import Path
from fractions import Fraction as F
from math import isqrt
import hashlib
import json
import window_interval_kernel as ik
import window_phase_coefficients as provider

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def amp(x):
    px = ik.PI * F(x)
    return ik.COSTH * px / (ik.Z * (px.square()-F(1, 2)))


def upward_sqrt(x):
    scale = 10**20
    k = isqrt(x.numerator*scale**2//x.denominator)
    if F(k, scale)**2 < x:
        k += 1
    v = F(k, scale)
    assert (v-F(1, scale))**2 < x <= v*v
    return v


def main():
    packet_path = HERE/'window_phase_lattice_rigidity_probe.json'
    d = json.loads(packet_path.read_bytes())
    parameter = ROOT/'research-20261016-followup/window_reweight_rational.json'
    p = json.loads(parameter.read_bytes())
    assert d['parameter_sha256'] == sha(parameter)
    assert d['script_sha256'] == sha(HERE/'window_phase_lattice_rigidity_probe.py')
    assert d['interval_kernel_sha256'] == sha(HERE/'window_interval_kernel.py')
    assert d['phase_packet_provider_sha256'] == sha(HERE/'window_phase_coefficients.py')
    assert d['phase_packet_Taylor_data_sha256'] == sha(ROOT/'StructuralGoal20261016/WindowJetTableData.lean')
    a = {(i, j): F(v, p['denominator']) for i, j, v in p['a_upper'] if v}
    b = [F(v, p['denominator']) for v in p['b_numerators']]
    sep, c = F(123, 128), F(11, 1250)
    g = [F(9, 4)]+[F(1)]*8
    positions = [F(0)]
    for x in g:
        positions.append(positions[-1]+x)
    pressure = sum(x*y for x, y in zip(b, g))
    q = ik.I(0)
    for (i, j), weight in a.items():
        if i == 0:
            q += weight*amp(positions[j]-positions[i]).square()/2
    # Every nonzero sine here is an integer-plus-quarter angle; sin^2=1/2.
    assert min(g) >= sep and F(1, 4) > F(21, 100)
    assert pressure == F(4678584775, 10**12)
    assert q.u+pressure <= F(7480552872134, 10**15) < c
    point = d['rank_one_counterexample']
    assert list(map(F, point['gaps'])) == g
    assert list(map(F, point['positions'])) == positions

    excess = c-sep*sum(b)
    coefficient_l2 = sum(F(x, 10**9)**2 for x in p['window_coefficient_numerators_1e9'])
    rcap, hsum = F(0), F(0)
    for row, ((i, j), weight) in zip(d['root_edges'], a.items()):
        lo = (j-i)*sep
        hi = lo+excess/min(b[i:j])
        assert list(map(F, [row['lower_span'], row['upper_span']])) == [lo, hi]
        ab = amp(hi)
        assert list(map(F, row['A_at_upper_enclosure'])) == [ab.l, ab.u]
        cb2 = (ik.I(coefficient_l2/2)*(F(1, 2)+ik.I(1)/(4*ik.PI*lo))/ik.Z.square()).u
        cc = upward_sqrt(cb2)
        bc = (ik.I(1)/(2*(ik.PI*lo).square()-1)).u
        assert cc == F(row['C_absolute_upper']) and bc == F(row['B_absolute_upper'])
        rcap += weight*(bc+cc)**2
        hsum += weight*ab.l**2
    recorded_cap = list(map(F, d['root_residual_squared_cap_enclosure']))
    assert recorded_cap[0] <= rcap <= recorded_cap[1]
    assert hsum == F(d['root_safe_conductance_sum_exact']) and rcap > hsum

    t = d['signed_triangle_packet']
    packets = t['uniform_ratio_packets']
    fresh = provider.Provider()
    domains = [(31488, 39650), (62976, 72418)]
    replayed = 0
    for lo, hi in domains:
        covered = lo
        lower = F(257, 10000) if lo == 31488 else F(-89, 1000)
        for row in [r for r in packets if lo <= r['lower_units'] < hi]:
            left, right = row['lower_units'], row['upper_units']
            assert left == covered and left < right <= hi
            n, radius, values = fresh.amplitudes(F(left, 32768), F(right, 32768))
            ratio = values[2]/values[0]
            assert n == row['integer_center'] and ratio.ints() == row['C_over_A_Q30']
            assert F(ratio.l, provider.Q) >= lower
            covered = right
            replayed += 1
        assert covered == hi
    assert replayed == len(packets) == 18
    cosine = ik.interval.sin_interval(ik.PI/2+ik.PI*F(21, 100))
    assert cosine.l >= F(79, 100)
    h = ik.Z/(2*ik.PI*ik.COSTH)
    cost = h.l*(4*F(79, 100)**2-1)/F(221, 100)+2*F(257, 10000)*F(79, 100)-F(89, 1000)
    assert cost == F(t['absolute_signed_frustration_lower']) > F(2, 25)
    aa, az = amp(F(121, 100)).l, amp(F(221, 100)).l
    denom = 1/(a[1, 2]*aa*aa)+1/(a[2, 3]*aa*aa)+1/(a[1, 3]*az*az)
    lower = cost*cost/denom
    assert denom == F(t['Cauchy_denominator_upper'])
    assert lower == F(t['triangle_weighted_kernel_energy_lower']) > F(1, 100000)
    out = {
        'scope': __doc__, 'script_sha256': sha(Path(__file__)),
        'producer_receipt_sha256': sha(packet_path),
        'parameter_sha256': sha(parameter), 'passed': True,
        'root_edges_checked': len(a), 'uniform_Taylor_packets_checked': replayed,
        'rank_one_localization_counterexample_checked': True,
        'root_global_payment_vacuous_checked': True,
        'signed_cycle_local_energy_lower': str(lower),
        'shared_interval_provider_analytic_bounds_independently_reproved': False,
        'actual_Lean_exclusion_proven': False, 'global_floor_proven': False,
        'new_zero_proportion_proven': False, 'website_submission_ready': False,
    }
    target = HERE/'window_phase_lattice_rigidity_replay.json'
    target.write_text(json.dumps(out, indent=2)+'\n', encoding='utf8')
    print(json.dumps({'passed': True, 'root_edges': len(a), 'Taylor_packets': replayed,
                      'receipt_sha256': sha(target)}))


if __name__ == '__main__':
    main()
