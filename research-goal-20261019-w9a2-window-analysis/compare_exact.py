"""One deterministic rational comparison; no optimization or Lean acceptance claim."""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal, localcontext
import ast
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
NEW = ROOT / 'research-goal-20261019-w9a2-record/official/proof/Solution.lean'
OLD = ROOT / 'submission/single-exception-overlap-accepted-20261019/proof/Solution.lean'

def dec(q):
    with localcontext() as ctx:
        ctx.prec = 65
        return str(Decimal(q.numerator) / Decimal(q.denominator))

def data(q):
    return {'numerator': str(q.numerator), 'denominator': str(q.denominator), 'decimal': dec(q)}

def extract(path):
    text = path.read_text(encoding='utf-8')
    coeff = text.split('def cAMn :', 1)[1].split('def cAM (', 1)[0]
    coeff = {int(j): int(c) for j, c in re.findall(r'\| (\d+) => (-?\d+)', coeff)}
    cert = text.split('namespace AMW.Cert.PC9QB6M', 1)[1]
    bs = ast.literal_eval(re.search(r'def BS : List ℕ := (\[[^\n]+\])', cert)[1])
    ts = ast.literal_eval(re.search(r'def TS : List Term := (\[[^\n]+\])', cert)[1])
    return {'path': str(path.relative_to(ROOT)).replace('\\', '/'),
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'coefficients_numerator_over_1e9': [coeff[j] for j in range(13)],
            'BS_numerator_over_1e20': bs, 'TS': ts,
            'span_capacity': [data(sum((F(a, 10**20) for i, j, a, _ in ts if j-i == s), F(0))) for s in range(1, 9)]}

old = extract(OLD)
new = extract(NEW)
H0 = F(6721290091768038344368273523390880473594, 10**40)
H1 = F(6721237468782417141365717707344332375586, 10**40)
B0 = F(sum(old['BS_numerator_over_1e20']), 10**20)
B1 = F(sum(new['BS_numerator_over_1e20']), 10**20)
c0base = F(893616123055294719, 10**20)
c0 = c0base + F(389500523, 10**20)
c1 = F(893029029923108825, 10**20)
k = lambda h,b,c: (h-b)/(1-c)
K0 = k(H0, B0, c0)
K1 = k(H1, B1, c1)
assert K0 == F(3337839448633819172184136761695440236797, 4955319193827760237900000000000000000000)
assert K1 == F(3337881639516708570682858853672166187793, 4955348548503844558750000000000000000000)
assert B0 == F(456111945004000000, 10**20)
assert B1 == F(454741897490, 10**14)
steps = [K0, k(H1,B0,c0), k(H1,B1,c0), K1]
terms = [steps[i+1]-steps[i] for i in range(3)]
assert sum(terms, F(0)) == K1-K0

out = {
    'scope': 'Static source extraction and exact rational identities only. No search, no new formal theorem, no kernel replay.',
    'old': old, 'new': new,
    'H_old': data(H0), 'H_new': data(H1), 'H_delta': data(H1-H0),
    'B_old': data(B0), 'B_new': data(B1), 'B_delta': data(B1-B0),
    'c_old_base': data(c0base), 'c_old_accepted': data(c0), 'c_new': data(c1), 'c_delta': data(c1-c0),
    'K_old': data(K0), 'K_new': data(K1),
    'gain_proportion': data(K1-K0), 'gain_percentage_points': data(100*(K1-K0)),
    'relative_gain_to_previous_tiny_gain': data((K1-K0)/(K0-k(H0,B0,c0base))),
    'ordered_counterfactual_warning': 'The H/B/c attribution depends on the stated order; the sum is exact. Intermediate ratios are algebraic counterfactuals, not proved zeta bounds.',
    'ordered_attribution_H_then_B_then_c': [
        {'changed': name, 'proportion': data(term), 'percentage_points': data(100*term)}
        for name, term in zip(['H', 'B', 'c'], terms)
    ],
    'local_sensitivity_dK_dc_at_new': data(K1/(1-c1)),
    'threshold_67_36_percent_if_H_B_fixed': {
        'target_K': data(F(6736,10000)),
        'required_c': data(1-(H1-B1)/F(6736,10000)),
        'required_c_increase': data(1-(H1-B1)/F(6736,10000)-c1),
        'warning': 'This is a required average floor, not an established feasible bound.'
    }
}
(Path(__file__).parent/'comparison.json').write_text(json.dumps(out, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
print(json.dumps({key: out[key] for key in ['H_delta','B_delta','c_delta','gain_percentage_points','ordered_attribution_H_then_B_then_c','threshold_67_36_percent_if_H_B_fixed']}, ensure_ascii=False, indent=2))
