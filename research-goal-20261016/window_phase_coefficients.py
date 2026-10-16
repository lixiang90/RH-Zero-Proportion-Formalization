"""Uniform rational w' phase-coefficient packets for two fixed residual cells.

This is a new Python interval provider, not a Lean proof. Frozen normalized
k/base coefficients are read without modification. C_all=k-kMT is evaluated
by integer-centred Taylor polynomials with the explicit derivative remainder
D*pi^24/(25*Z). Every cell span is fully partitioned at a 1/32 grid. No sampled
maximum is used as a uniform upper bound. No optimizer or Lean process runs.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
from functools import lru_cache
import argparse
import gzip
import hashlib
import json
import re
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SC = 32768
DS = 10**15
Q = 10**30
ORDER = 24
STEP = SC//32


def floor(x):
    x = F(x)
    return x.numerator//x.denominator


def ceil(x):
    return -floor(-F(x))


class RI:
    """Fixed-grid rational intervals, with outward integer rounding."""
    __slots__ = ('l', 'u')

    def __init__(self, l, u=None):
        self.l = floor(F(l)*Q)
        self.u = ceil(F(l if u is None else u)*Q)
        assert self.l <= self.u

    @classmethod
    def raw(cls, l, u):
        z = object.__new__(cls)
        z.l, z.u = int(l), int(u)
        assert z.l <= z.u
        return z

    @staticmethod
    def lift(x):
        return x if isinstance(x, RI) else RI(x)

    def __add__(self, x):
        x = RI.lift(x)
        return RI.raw(self.l+x.l, self.u+x.u)

    __radd__ = __add__

    def __neg__(self):
        return RI.raw(-self.u, -self.l)

    def __sub__(self, x):
        return self+-RI.lift(x)

    def __rsub__(self, x):
        return RI.lift(x)+-self

    def __mul__(self, x):
        x = RI.lift(x)
        p = [self.l*x.l, self.l*x.u, self.u*x.l, self.u*x.u]
        return RI.raw(min(p)//Q, -((-max(p))//Q))

    __rmul__ = __mul__

    def __truediv__(self, x):
        x = RI.lift(x)
        assert x.l*x.u > 0
        p = [F(a*Q, b) for a in (self.l, self.u) for b in (x.l, x.u)]
        return RI.raw(floor(min(p)), ceil(max(p)))

    def square(self):
        a = 0 if self.l <= 0 <= self.u else min(self.l*self.l, self.u*self.u)
        b = max(self.l*self.l, self.u*self.u)
        return RI.raw(a//Q, -((-b)//Q))

    def expand(self, error):
        e = ceil(F(error)*Q)
        return RI.raw(self.l-e, self.u+e)

    def bounds(self):
        return [str(F(self.l, Q)), str(F(self.u, Q))]

    def ints(self):
        return [self.l, self.u]


PI = RI(F(314159265358979323846, 10**20), F(314159265358979323847, 10**20))
THETA = RI(F(707106781186547524400844362104, 10**30),
           F(707106781186547524400844362105, 10**30))
SINTH = RI(F(649636939080062444129454621098, 10**30),
           F(649636939080062444132, 10**21))
COSTH = RI(F(760244597075630151252, 10**21),
           F(760244597075630151253567702555, 10**30))
Z = SINTH/THETA
BIGK = PI*COSTH/Z


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def canonical(x):
    return json.dumps(x, sort_keys=True, separators=(',', ':')).encode('utf8')


def parse_table(text, name):
    block = text.split('def '+name+' :', 1)[1].split('\ndef ', 1)[0]
    numbers = re.findall(r'qi30\s*\((-?\d+)\)\s*\((-?\d+)\)', block)
    assert len(numbers) % 24 == 0
    values = [RI.raw(int(l), int(u)) for l, u in numbers]
    return [values[j:j+24] for j in range(0, len(values), 24)]


def horner(cs, delta):
    answer = RI(0)
    for c in reversed(cs):
        answer = answer*delta+c
    return answer


def hull(rows):
    return RI.raw(min(x.l for x in rows), max(x.u for x in rows))


def quantize(x):
    return x.l*DS//Q, -((-x.u*DS)//Q)


def phase_at_integer_delta(n, delta):
    """Point-only consistency diagnostic; never a uniform payment source."""
    sn, cs = [], []
    power = RI(1)
    for r in range(40):
        if r:
            power = power*PI/r
        sn.append(power*[0, 1, 0, -1][r % 4]*((-1)**n))
        cs.append(power*[1, 0, -1, 0][r % 4]*((-1)**n))
    rem = F(PI.u, Q)**40*abs(delta)**40/factorial(40)
    return horner(sn, RI(delta)).expand(rem), horner(cs, RI(delta)).expand(rem)


class Provider:
    def __init__(self):
        self.parameter_path = ROOT/'research-20261016-followup/window_reweight_rational.json'
        self.parameters = json.loads(self.parameter_path.read_bytes())
        self.data_path = ROOT/'StructuralGoal20261016/WindowJetTableData.lean'
        text = self.data_path.read_text(encoding='utf8')
        self.k = parse_table(text, 'kValues')
        self.base = parse_table(text, 'baseValues')
        assert len(self.k) == 33 and len(self.base) == 66
        self.coefficients = [F(v, 10**9) for v in
                             self.parameters['window_coefficient_numerators_1e9']]
        self.D = sum(map(abs, self.coefficients))
        assert self.D == F(78742791, 10**9)
        self.M24 = self.D*F(PI.u, Q)**24/(25*F(Z.l, Q))
        self.terms = [(int(i), int(j), int(a)) for i, j, a in self.parameters['a_upper']
                      if int(a) > 0]
        assert len(self.terms) == 41 and self.parameters['denominator'] == 10**10
        self.all_pairs = [(i, i+1) for i in range(9)]
        self.all_pairs += [(i, j) for i in range(10) for j in range(i+1, 10) if j-i != 1]
        assert len(self.all_pairs) == 45 and len(set(self.all_pairs)) == 45
        self.lookup = {pair: k for k, pair in enumerate(self.all_pairs)}
        self.c = {n: [self.k[n][r]-(self.base[2*n][r]+self.base[2*n+1][r])/(2*Z)
                       for r in range(24)] for n in range(1, 33)}
        self.remainders = {}

    def remainder(self, radius_units):
        key = str(radius_units)
        if key not in self.remainders:
            radius = F(radius_units, SC)
            self.remainders[key] = {
                'radius_units': radius_units, 'radius': str(radius),
                'C_error': str(self.M24*radius**24/factorial(24)),
                'Cprime_error': str(self.M24*radius**23/factorial(23))}
        return self.remainders[key]

    def amplitudes(self, lo, hi):
        assert F(123, 128) <= lo <= hi
        n = floor((lo+hi)/2+F(1, 2))
        assert 1 <= n <= 32
        radius = max(abs(lo-n), abs(hi-n))
        assert radius <= F(1, 2)
        radius_units = radius*SC
        assert radius_units.denominator == 1
        rem = self.remainder(int(radius_units))
        delta = RI(lo-n, hi-n)
        c = horner(self.c[n], delta).expand(F(rem['C_error']))
        cp = horner([(r+1)*self.c[n][r+1] for r in range(23)], delta).expand(F(rem['Cprime_error']))
        x = RI(lo, hi)
        px2 = PI.square()*x.square()
        den = px2-F(1, 2)
        assert den.l > 0
        a = BIGK*x/den
        ap = -(BIGK*(px2+F(1, 2)))/den.square()
        b = -RI(F(1, 2))/den
        bp = PI.square()*x/den.square()
        return n, radius_units.numerator, [a, b, c, ap, bp, cp]

    @staticmethod
    def alpha(amplitudes):
        a, b, c, ap, bp, cp = amplitudes
        return [2*c*cp+a*ap+b*bp,
                2*(cp*b+c*bp)+2*PI*c*a,
                2*(cp*a+c*ap)-2*PI*c*b,
                b*bp-a*ap+2*PI*a*b,
                ap*b+a*bp-PI*(b.square()-a.square())]

    def row(self, t, i, j, weight, low_units, high_units):
        assert low_units <= high_units
        cuts = [low_units]+list(range((low_units//STEP+1)*STEP, high_units, STEP))+[high_units]
        pieces = []
        results = [[] for _ in range(5)]
        amp_results = [[] for _ in range(6)]
        digest = hashlib.sha256()
        for lu, uu in zip(cuts, cuts[1:]):
            n, ru, amps = self.amplitudes(F(lu, SC), F(uu, SC))
            alphas = self.alpha(amps)
            pieces.append([lu, uu, n, ru])
            for r, a in enumerate(alphas):
                results[r].append(a)
            for r, a in enumerate(amps):
                amp_results[r].append(a)
            digest.update(canonical({'piece': pieces[-1],
                'amplitude_endpoints_Q30': [a.ints() for a in amps],
                'alpha_endpoints_Q30': [a.ints() for a in alphas]}))
        if low_units == high_units:
            n, ru, amps = self.amplitudes(F(low_units, SC), F(high_units, SC))
            alphas = self.alpha(amps)
            pieces = [[low_units, high_units, n, ru]]
            results, amp_results = [[a] for a in alphas], [[a] for a in amps]
        bounded = [hull(vs) for vs in results]
        lower, upper = zip(*(quantize(a) for a in bounded))
        # The reference is evaluated at a rational grid point inside the span.
        # An SC-grid point also keeps every Taylor radius exactly catalogued.
        ref_units = (low_units+high_units)//2
        ref = F(ref_units, SC)
        n, _, amps = self.amplitudes(ref, ref)
        reference_intervals = self.alpha(amps)
        refs = [floor(F(a.l+a.u, 2*Q)*DS+F(1, 2)) for a in reference_intervals]
        errors = [max(v-l, u-v) for l, u, v in zip(lower, upper, refs)]
        assert all(e >= 0 for e in errors)
        # Independent point identity: actual w'=2*k*k' from frozen k jets,
        # versus the five-harmonic formula. This is only a sign diagnostic.
        delta = ref-n
        sn, cs = phase_at_integer_delta(n, delta)
        basis = [RI(1), cs, sn, cs.square()-sn.square(), 2*sn*cs]
        predicted = sum((a*b for a, b in zip(reference_intervals, basis)), RI(0))
        totalM = F(PI.u, Q)**24
        kval = horner(self.k[n], RI(delta)).expand(totalM*abs(delta)**24/factorial(24))
        kp = horner([(r+1)*self.k[n][r+1] for r in range(23)], RI(delta)).expand(
            totalM*abs(delta)**23/factorial(23))
        mismatch = predicted-2*kval*kp
        assert mismatch.l <= 0 <= mismatch.u, (t, n, ref, mismatch.bounds())
        return {
            't': t, 'i': i, 'j': j, 'weight_numerator': weight,
            'l': str(F(low_units, SC)), 'u': str(F(high_units, SC)),
            'l_units': low_units, 'u_units': high_units,
            'reference_x': str(ref), 'reference_x_units': ref_units,
            'reference': [str(F(v, DS)) for v in refs],
            'lower': [str(F(v, DS)) for v in lower],
            'upper': [str(F(v, DS)) for v in upper],
            'error': [str(F(v, DS)) for v in errors],
            'reference_numerators': refs, 'lower_numerators': list(lower),
            'upper_numerators': list(upper), 'error_numerators': errors,
            'prequantized_alpha_endpoints_Q30': [a.ints() for a in bounded],
            'amplitude_hulls_Q30': [hull(vs).ints() for vs in amp_results],
            'pieces_units': pieces,
            'uniform_derivation_sha256': digest.hexdigest(),
            'reference_derivative_identity_difference': mismatch.bounds(),
            'reference_identity_consistent': True}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--case', type=int, choices=[0, 1], required=True)
    args = ap.parse_args()
    start = time.monotonic()
    provider = Provider()
    source_path = HERE/'cover-curvature-parent64.input.json.gz'
    selection_path = HERE/'cover-lifted-graph-energy8.json'
    packed = source_path.read_bytes()
    selection = json.loads(selection_path.read_bytes())
    assert selection['receipt']['input_sha256'] == sha(packed)
    all_cases = {r['path']: r for r in json.loads(gzip.decompress(packed))['cases']}
    path = selection['rows'][args.case]['path']
    state = all_cases[path]['before']
    assert len(state) == 2 and len(state[0]) == len(state[1]) == 45
    terms = []
    for t, (i, j, weight) in enumerate(provider.terms):
        pair_index = provider.lookup[i, j]
        terms.append(provider.row(t, i, j, weight,
                     int(state[0][pair_index]), int(state[1][pair_index])))
    sources = [source_path, selection_path, provider.parameter_path, provider.data_path,
        ROOT/'StructuralGoal20261016/WindowIntegerJetRecipe.lean',
        ROOT/'StructuralGoal20261016/WindowFixedTablesAll.lean',
        ROOT/'StructuralGoal20261016/WindowNormalizedJets.lean',
        ROOT/'StructuralGoal20261016/WindowKernel.lean',
        ROOT/'StructuralGoal20261016/WindowEnergy.lean',
        HERE/'window_phase_hermitian_audit.txt']
    centers = sorted({p[2] for row in terms for p in row['pieces_units']})
    packet = {
        'schema': 'uniform-phase-derivative-coefficients-v1',
        'scope': __doc__, 'SC': SC, 'DS': DS, 'scale': DS, 'arithmetic_scale': Q,
        'alpha_order': ['constant', 'cos(pi*x)', 'sin(pi*x)', 'cos(2*pi*x)', 'sin(2*pi*x)'],
        'amplitude_order': ['A0', 'B', 'C_all', 'A0prime', 'Bprime', 'C_allprime'],
        'parameters_sha256': sha(provider.parameter_path.read_bytes()),
        'input_sha256': sha(packed), 'selection_sha256': sha(selection_path.read_bytes()),
        'source_sha256': sha(Path(__file__).read_bytes()),
        'inputs': [{'path': str(p.relative_to(ROOT)).replace('\\', '/'),
                    'sha256': sha(p.read_bytes())} for p in sources],
        'elementary_inputs': {name: value.bounds() for name, value in
            [('pi', PI), ('theta', THETA), ('sin_theta', SINTH), ('cos_theta', COSTH), ('Z', Z)]},
        'analytic_basis': {
            'decomposition': 'k=C_all+A0*sin(pi*x)+B*cos(pi*x); C_all=k-KMT/Z',
            'domain': 'x>=123/128; MT poles +/-theta/pi are excluded',
            'normalized_coefficients': 'C_r=K(n,r)-(Base(n,false,r)+Base(n,true,r))/(2Z); each r is derivative/r!',
            'C24_bound': 'D*pi^24/(25*Z) from the perturbation Fourier integral and integral|t|^24=1/(2^24*25)',
            'D': str(provider.D), 'C24_uniform_rational_upper': str(provider.M24),
            'C_taylor_degree': 23, 'Cprime_taylor_degree': 22,
            'C_error': 'M24*radius^24/24!', 'Cprime_error': 'M24*radius^23/23!',
            'coverage': 'All contiguous pieces partition [l,u]; each lies in |x-n|<=1/2. Endpoint hull is uniform, not sampled.',
            'formula': ['2*C*Cprime+A*Aderiv+B*Bderiv',
                '2*(Cprime*B+C*Bderiv)+2*pi*C*A',
                '2*(Cprime*A+C*Aderiv)-2*pi*C*B',
                'B*Bderiv-A*Aderiv+2*pi*A*B',
                'Aderiv*B+A*Bderiv-pi*(B^2-A^2)'],
            'remainder_catalog_units': SC,
            'sample_maxima_used_as_upper_bounds': False,
            'new_amplitude_and_coefficient_interfaces_Lean_proven': False},
        'C_normalized_coefficient_endpoints_Q30': {
            str(n): [a.ints() for a in provider.c[n]] for n in centers},
        'remainder_catalog': provider.remainders,
        'cases': [{'case_index': args.case, 'path': path, 'cell': state, 'terms': terms}],
        'diagnostics': {
            'all_41_reference_derivative_identities_consistent': True,
            'pieces': sum(len(r['pieces_units']) for r in terms),
            'max_coefficient_error': float(max(F(v) for r in terms for v in r['error'])),
            'elapsed_seconds': time.monotonic()-start},
        'outward_rational_interval_computation': True,
        'lean_verified': False, 'independent_kernel_verified': False,
        'strict_phase_KKT_certificate_proven': False,
        'complete_global_cover': False, 'new_zero_proportion_proven': False}
    target = HERE/f'window_phase_coefficients_case{args.case}.json'
    assert not target.exists(), 'Packets are immutable after creation; use a new version path to revise.'
    target.write_text(json.dumps(packet, separators=(',', ':'))+'\n', encoding='utf8')
    print(json.dumps({'case': args.case, 'path': path, 'file': str(target),
        'sha256': sha(target.read_bytes()), 'bytes': target.stat().st_size,
        **packet['diagnostics'], 'Lean_proven': False}), flush=True)


if __name__ == '__main__':
    main()
