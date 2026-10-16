"""Independent rational enclosures for the frozen replacement windows.

Reads the new coefficients, not the discovery optimizer. Uses a separate
Machin/sin-103 interval implementation, not the inherited Taylor decoder.
This checks analytic numerical inputs; it proves no whole-domain floor.
"""
from pathlib import Path
from fractions import Fraction as F
from math import comb
import hashlib, json, re

import global_periodic_upper_bound as independent

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
I = independent.I
PI, SQRT2 = independent.PI, independent.SQRT2
sin = independent.sin_interval


def main():
    source = HERE / 'window_exact_parameters.json'
    inputs = [source, HERE/'global_periodic_upper_bound.py',
              ROOT/'StructuralW10Followup20261016/NewWindows.lean']
    hashes = {str(p.relative_to(ROOT)): sha(p) for p in inputs}
    doc = json.loads(source.read_text())
    lean = inputs[-1].read_text(encoding='utf8')
    theta = SQRT2/2
    sn, cs = sin(theta), sin(PI/2+theta)
    norm = 2*sn/SQRT2
    rows = []
    for row in doc['windows']:
        nums = row['coefficient_numerators']
        m, den = len(nums), row['coefficient_denominator']
        block = lean.split(f'def nums{m} : ℕ → ℤ\n', 1)[1].split('  | _ => 0', 1)[0]
        assert [int(v) for v in re.findall(r'\| \d+ => (-?\d+)', block)] == nums
        coeff = [F(n, den) for n in nums]
        l1 = sum(map(abs, coeff))
        assert l1 == F(row['sum_abs_coefficients_exact']) < F(2, 25)
        pam = I(0)
        for j, c in enumerate(coeff, 1):
            pam += c*c*(I(F(1, 2))-I(1)/(4*PI.square()*j*j))
        hh = I(F(3, 2))-cs/norm-pam/norm.square()
        assert F(row['rounded_H_lower']) <= hh.l
        assert F(row['exact_analytic_H_lower_expression']) <= hh.l
        assert hh.u <= F(row['exact_analytic_H_upper_expression'])
        cut = F(row['small_pair_bound']['cut'])
        p = PI*cut
        kval = sin(p+theta)/(2*p+SQRT2)+sin(p-theta)/(2*p-SQRT2)
        for j, c in enumerate(coeff, 1):
            kval += c*((-1)**j)*sin(p)*cut/(PI*(cut*cut-j*j))
        kval = kval/norm
        w = kval.square()
        assert F(row['small_pair_bound']['kernel_lower']) <= kval.l
        assert F(row['small_pair_bound']['w_lower']) <= w.l
        c = F(row['proposed_local_floor'])
        pressure = F(row['pressure_sum'])
        score = (F(row['rounded_H_lower'])-pressure)/(1-c)
        assert score == F(row['conditional_kappa_exact'])
        rows.append({'modes': m, 'sum_abs_exact': str(l1),
                     'H_interval': [str(hh.l), str(hh.u)],
                     'kernel_cut_interval': [str(kval.l), str(kval.u)],
                     'w_cut_interval': [str(w.l), str(w.u)],
                     'H_lower_from_parameters_verified': True,
                     'pair_endpoint_lower_verified': True,
                     'conditional_score_exact_verified': True,
                     'whole_domain_floor_verified': False})
    majorant = doc['majorant']
    power = list(map(F, majorant['majorant_gap_power_coefficients']))
    beta = [sum(power[i]*F(1, 4)**i*F(comb(k, i), comb(6, i))
                for i in range(k+1)) for k in range(7)]
    assert beta == list(map(F, majorant['bernstein_coefficients']))
    assert min(beta) > F(1, 40)
    assert hashes == {str(p.relative_to(ROOT)): sha(p) for p in inputs}
    out = {'scope': __doc__, 'input_sha256': hashes,
           'script_sha256': sha(Path(__file__)), 'windows': rows,
           'majorant_bernstein_reconstruction_passed': True,
           'all_checks_passed': True, 'new_zero_proportion_proven': False}
    (HERE/'window_independent_audit.json').write_text(json.dumps(out, indent=2)+'\n', encoding='utf8')
    print(json.dumps({'passed': True, 'windows': [r['modes'] for r in rows],
                      'bernstein_min': str(min(beta)), 'new_zero_proportion_proven': False}))


if __name__ == '__main__':
    main()
