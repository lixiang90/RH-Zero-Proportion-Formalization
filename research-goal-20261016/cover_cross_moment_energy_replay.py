"""Independent stdlib replay of quadratic energy moment-row packets.

Recompute whole-span w'' lower bounds from the independent Taylor checker,
anchor feasibility, uniform gradient-error payment, all quadratic row
coefficients, and factorized polynomial identities. Stored point F/gradient
intervals are inputs: their kernel evaluations are deliberately not rerun.
This is a finite packet/algebra audit, not a new Lean proof, floating LP
feasibility certificate, or zero-proportion improvement.
"""
from pathlib import Path
from fractions import Fraction as F
import gzip
import hashlib
import json
import time

import cover_correlated_curvature_verify as scalar

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SC, DS = scalar.SC, scalar.DS
PAIRS = [(r, s) for r in range(9) for s in range(r, 9)]
HI = {pair: 50+k for k, pair in enumerate(PAIRS)}
V = 464
sha = lambda raw: hashlib.sha256(raw).hexdigest()


def verify_packet(state, packet, params, checker):
    scalar.a.closure_valid(state)
    point = list(map(F, packet['centre']))
    assert len(point) == 9
    assert all(F(l, SC) <= sum(point[i:j]) <= F(u, SC)
               for (i, j), l, u in zip(scalar.a.PAIRS, *state))
    lo, hi = [[F(x, SC) for x in row[:9]] for row in state]
    mid = [(a+b)/2 for a, b in zip(lo, hi)]
    rad = [(b-a)/2 for a, b in zip(lo, hi)]
    assert all(r > 0 for r in rad)
    f0 = list(map(F, packet['F_interval']))
    grad = [list(map(F, interval)) for interval in packet['gradient_interval']]
    assert len(f0) == 2 and f0[0] <= f0[1] and len(grad) == 9
    assert all(len(v) == 2 and v[0] <= v[1] for v in grad)
    gm = [(a+b)/2 for a, b in grad]
    payment = sum((u-l)/2*max(abs(a-c), abs(b-c))
                  for (l, u), a, b, c in zip(grad, lo, hi, point))
    assert payment == F(packet['uniform_gradient_error_payment'])
    terms = [tuple(t) for t in params['a_upper'] if t[2]]
    assert len(terms) == len(packet['whole_span_second_lower']) == 41
    lower = []
    for (i, j, aw), stored in zip(terms, packet['whole_span_second_lower']):
        z = scalar.a.INDEX[i, j]
        l, u = state[0][z], state[1][z]
        assert 0 <= l <= u <= 32*SC
        first = l//checker.width
        last = (max(l+1, u)+checker.width-1)//checker.width
        value = F(min(checker.second[k][0] for k in range(first, last)), DS)
        assert value == F(stored)
        lower.append(value)
    # Construct directly in physical g coordinates first, independently
    # of the producer's intermediate y linear/constant rearrangement.
    expected = [F(0)]*V
    constant = f0[0]-payment-sum(v*c for v, c in zip(gm, point))
    expected[:9] = gm
    for (i, j, aw), L in zip(terms, lower):
        weight = F(aw, params['denominator'])*L/2
        delta0 = sum(mid[i:j])-sum(point[i:j])
        # (delta0+sum rad_r*y_r)^2; replace y_r by
        # (g_r-mid_r)/rad_r only for its linear part.
        constant += weight*delta0**2
        for r in range(i, j):
            expected[r] += 2*weight*delta0
            constant -= 2*weight*delta0*mid[r]
            for s in range(r, j):
                expected[HI[r, s]] += (1 if r == s else 2)*weight*rad[r]*rad[s]
    assert constant == F(packet['quadratic_constant'])
    stored = [F(0)]*V
    seen = set()
    for k, value in packet['row']:
        assert isinstance(k, int) and 0 <= k < V and k not in seen
        seen.add(k)
        stored[k] = F(value)
        assert stored[k]
    assert expected == stored
    assert F(packet['bound']) == F(11, 1250)-constant
    identity_checks = 0
    for n in range(5):
        ys = [F(-1) if n == 0 else F(1) if n == 1 else F((r*(n+1)) % 11-5, 5)
              for r in range(9)]
        g = [m+r*y for m, r, y in zip(mid, rad, ys)]
        direct = f0[0]-payment+sum(v*(x-c) for v, x, c in zip(gm, g, point))
        direct += sum(F(aw, params['denominator'])*L*sum(g[r]-point[r] for r in range(i, j))**2/2
                      for (i, j, aw), L in zip(terms, lower))
        lifted = constant+sum(expected[r]*g[r] for r in range(9))
        lifted += sum(expected[HI[r, s]]*ys[r]*ys[s] for r, s in PAIRS)
        assert direct == lifted
        identity_checks += 1
    ys0 = [(c-m)/r for c, m, r in zip(point, mid, rad)]
    anchor = constant+sum(expected[r]*point[r] for r in range(9))
    anchor += sum(expected[HI[r, s]]*ys0[r]*ys0[s] for r, s in PAIRS)
    assert anchor == f0[0]-payment and packet['centre_factorization_exact']
    return {'passed': True, 'strict_anchor_DBM_checks': 45, 'whole_span_second_lower_checks': 41,
            'rational_row_entries_compared': V, 'factorized_polynomial_identities': identity_checks,
            'anchor_identity_passed': True, 'point_kernel_intervals_recomputed': False}


def main():
    started = time.monotonic()
    input_raw = (HERE/'cover-cross-moment-energy-two.json').read_bytes()
    document = json.loads(input_raw)
    producer_raw = (HERE/'cover_cross_moment_energy_probe.py').read_bytes()
    base_raw = (HERE/'cover_cross_moment_probe.py').read_bytes()
    cell_raw = (HERE/'cover-curvature-parent64.input.json.gz').read_bytes()
    table_raw = (HERE/'cover_newjet.json').read_bytes()
    params_raw = (ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes()
    sample_raw = (HERE/'cover-gradient-mixture.json').read_bytes()
    receipt = document['receipt']
    for key, raw in [('script_sha256', producer_raw), ('base_model_sha256', base_raw),
                     ('parent64_input_sha256', cell_raw), ('table_sha256', table_raw),
                     ('sample_input_sha256', sample_raw),
                     ('kernel_helper_sha256', (HERE/'window_interval_kernel.py').read_bytes())]:
        assert receipt[key] == sha(raw)
    cases = {c['path']: c for c in json.loads(gzip.decompress(cell_raw))['cases']}
    checker = scalar.CurvatureReplay(json.loads(table_raw))
    params = json.loads(params_raw)
    rows = []
    for row in document['rows']:
        assert len(row['energy_packets']) == row['added_energy_rows'] == 2
        rows.append({'path': row['path'], 'packets': [verify_packet(cases[row['path']]['before'], p, params, checker)
                                                     for p in row['energy_packets']]})
    assert len(rows) == 2
    out = {'scope': __doc__, 'script_sha256': sha(Path(__file__).read_bytes()),
           'input_sha256': sha(input_raw), 'producer_sha256': sha(producer_raw),
           'base_model_sha256': sha(base_raw), 'cell_input_sha256': sha(cell_raw),
           'table_sha256': sha(table_raw), 'parameters_sha256': sha(params_raw),
           'independent_scalar_checker_sha256': sha(Path(scalar.__file__).read_bytes()),
           'all_packet_checks_passed': True, 'cases': rows,
           'point_kernel_intervals_recomputed': False, 'floating_LP_primal_verified': False,
           'PSD_feasibility_proven': False, 'strict_certificates': 0,
           'quadratic_energy_consumer_Lean_proven': False,
           'complete_global_cover': False, 'new_zero_proportion_proven': False,
           'seconds': time.monotonic()-started}
    output = HERE/'cover-cross-moment-energy-replay.json'
    output.write_text(json.dumps(out, indent=2)+'\n', encoding='utf8')
    print(json.dumps({'all_packet_checks_passed': True, 'cases': len(rows), 'packets': 4,
                      'seconds': out['seconds'], 'receipt_sha256': sha(output.read_bytes())}), flush=True)


if __name__ == '__main__':
    main()
