"""Exact rational interval jets for the frozen redesigned Fourier kernel.

All transcendental enclosures use an independent Machin/sin implementation.
This program supplies rigorous numerical evidence, not a Lean proof. Its
Taylor derivative bound is an explicitly recorded analytic obligation.
"""
from pathlib import Path
from fractions import Fraction as F
from math import comb, factorial
import functools, hashlib, json, sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'research-20261016-followup'))
import global_periodic_upper_bound as interval

I = interval.I
PI, SQRT2 = interval.PI, interval.SQRT2
PARAM = ROOT/'research-20261016-followup/window_reweight_rational.json'
DATA = json.loads(PARAM.read_bytes())
COEFF = [F(1)] + [F(v, 10**9) for v in DATA['window_coefficient_numerators_1e9']]
THETA = SQRT2/2
SINTH = interval.sin_interval(THETA)
COSTH = interval.sin_interval(PI/2+THETA)
Z = 2*SINTH/SQRT2


def ipow(x, n):
    result = I(1)
    while n:
        if n & 1:
            result = result*x
        x = x*x
        n >>= 1
    return result


def sinc_jet(z, sn, cs, order):
    """Derivatives with respect to z, with a stable series around z=0."""
    if max(abs(z.l), abs(z.u)) <= F(4, 5):
        count = 48
        ans = []
        for r in range(order+1):
            value = I(0)
            for j in reversed(range(count)):
                sign = [1, 0, -1, 0][(r+j) % 4]
                value = value*z+F(sign, factorial(j)*(r+j+1))
            error = F(4, 5)**count/F(factorial(count)*(r+count+1))
            ans.append(I(value.l-error, value.u+error))
        return ans
    assert z.l*z.u > 0
    inv = I(1)/z
    powers = [inv]
    for _ in range(order):
        powers.append(powers[-1]*inv)
    phases = [sn, cs, -sn, -cs]
    ans = []
    for r in range(order+1):
        ans.append(sum((comb(r, j)*((-1)**(r-j))*factorial(r-j)*
                        phases[j % 4]*powers[r-j] for j in range(r+1)), I(0)))
    return ans


@functools.lru_cache(None)
def kernel_jet(point, order=1):
    point = F(point)
    px = PI*point
    sx = interval.sin_interval(px)
    cx = interval.sin_interval(PI/2+px)
    total = [I(0) for _ in range(order+1)]
    for sign in [-1, 1]:
        z = px+sign*THETA
        sn = sx*COSTH+sign*cx*SINTH
        cs = cx*COSTH-sign*sx*SINTH
        jets = sinc_jet(z, sn, cs, order)
        for r, value in enumerate(jets):
            total[r] += value
    for j, coef in enumerate(COEFF[1:], 1):
        if not coef:
            continue
        sn, cs = ((-1)**j)*sx, ((-1)**j)*cx
        for sign in [-1, 1]:
            jets = sinc_jet(PI*(point+sign*j), sn, cs, order)
            for r, value in enumerate(jets):
                total[r] += coef*value
    pi_power = I(1)
    ans = []
    for value in total:
        ans.append(value*pi_power/(2*Z))
        pi_power *= PI
    return tuple(ans)


def w_jet(point, order=1):
    ks = kernel_jet(F(point), order)
    return tuple(sum((comb(r, j)*ks[j]*ks[r-j] for j in range(r+1)), I(0))
                 for r in range(order+1))


def bernstein_lower(coeff, left, right):
    """Lower enclosure of a polynomial on [left,right] in Bernstein basis."""
    degree = len(coeff)-1
    power = [I(0) for _ in coeff]
    for j, value in enumerate(coeff):
        for k in range(j+1):
            power[k] += value*comb(j, k)*left**(j-k)*(right-left)**k
    beta = [sum((power[j]*F(comb(k, j), comb(degree, j)) for j in range(k+1)), I(0))
            for k in range(degree+1)]
    return min(v.l for v in beta)


def convex_certificate(center, left, right, pieces=8, order=16):
    """Taylor/positive-Bernstein evidence for w''≥0 on a rational interval.

    Uses the analytic inequality |w^(order)|≤(2*pi)^order coming from
    positivity of the normalized profile and its autocorrelation density.
    That generic inequality must still be connected in Lean.
    """
    center, left, right = map(F, [center, left, right])
    jets = w_jet(center, order-1)
    coeff = [jets[j+2]*F(1, factorial(j)) for j in range(order-2)]
    radius = max(abs(left-center), abs(right-center))
    remainder = F(44, 7)**order*radius**(order-2)/factorial(order-2)
    rows = []
    for k in range(pieces):
        l = left+(right-left)*F(k, pieces)
        u = left+(right-left)*F(k+1, pieces)
        lower = bernstein_lower(coeff, l-center, u-center)-remainder
        rows.append({'left': str(l), 'right': str(u), 'w_second_lower': str(lower)})
    return {'center': str(center), 'left': str(left), 'right': str(right),
            'jet_intervals': [[str(v.l), str(v.u)] for v in jets],
            'derivative_order': order, 'global_derivative_bound': str(F(44, 7)**order),
            'taylor_remainder': str(remainder), 'subintervals': rows,
            'positive': all(F(row['w_second_lower']) > 0 for row in rows),
            'minimum_lower': str(min(F(row['w_second_lower']) for row in rows))}


if __name__ == '__main__':
    import argparse, time
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-center', type=int, default=16)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    start = time.monotonic()
    rows = []
    for n in range(1, args.max_center+1):
        row = convex_certificate(n, F(n)-F(21, 100), F(n)+F(21, 100))
        rows.append(row)
        print(json.dumps({'center': n, 'positive': row['positive'],
                          'lower': float(F(row['minimum_lower'])),
                          'seconds': time.monotonic()-start}), flush=True)
    out = {'scope': __doc__, 'parameter_sha256': hashlib.sha256(PARAM.read_bytes()).hexdigest(),
           'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           'regions': rows, 'all_positive': all(row['positive'] for row in rows),
           'global_derivative_bound_Lean_proven': False,
           'local_floor_Lean_proven': False, 'new_zero_proportion_proven': False,
           'seconds': time.monotonic()-start}
    args.output.write_text(json.dumps(out, indent=2)+'\n', encoding='utf8')
