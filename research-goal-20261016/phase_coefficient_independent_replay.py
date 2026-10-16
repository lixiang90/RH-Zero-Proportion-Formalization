"""Independent exact replay of the two frozen uniform phase packets.

No import of window_phase_coefficients; no Lean, optimizer, or certificate
generation. This checks arithmetic and coverage only. The analytic bridge
for the new amplitudes and harmonics remains a paper-level obligation.
"""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import gzip
import hashlib
import json
import re
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
Q = 10**30
SC = 32768
DS = 10**15


def down(v):
    v = F(v)
    return v.numerator // v.denominator


def up(v):
    return -down(-F(v))


def interval(a, b=None):
    return (down(F(a)*Q), up(F(a if b is None else b)*Q))


def add(a, b):
    return a[0]+b[0], a[1]+b[1]


def neg(a):
    return -a[1], -a[0]


def sub(a, b):
    return add(a, neg(b))


def mul(a, b):
    products = tuple(x*y for x in a for y in b)
    return min(products)//Q, -((-max(products))//Q)


def div(a, b):
    assert 0 < b[0] or b[1] < 0
    endpoints = tuple(F(x*Q, y) for x in a for y in b)
    return down(min(endpoints)), up(max(endpoints))


def square(a):
    ends = (a[0]*a[0], a[1]*a[1])
    lower = 0 if a[0] <= 0 <= a[1] else min(ends)
    return lower//Q, -((-max(ends))//Q)


def scale(a, c):
    return mul(interval(c), a)


def expand(a, e):
    q = up(e*Q)
    return a[0]-q, a[1]+q


def polynomial(coefficients, x):
    total = interval(0)
    for c in reversed(coefficients):
        total = add(mul(total, x), c)
    return total


def envelope(values):
    return min(v[0] for v in values), max(v[1] for v in values)


def quantize(a):
    return a[0]*DS//Q, -((-a[1]*DS)//Q)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def canon(obj):
    return json.dumps(obj, sort_keys=True, separators=(',', ':')).encode()


def parse_rows(source, name, count):
    match = re.search(r'^def '+name+r' :[^=]+:= (.*?)(?=^def )', source,
                      re.M | re.S)
    assert match is not None
    pairs = [tuple(map(int, pair)) for pair in re.findall(
        r'qi30\s*\((-?\d+)\)\s*\((-?\d+)\)', match.group(1))]
    assert len(pairs) == count*24
    assert all(a <= b for a, b in pairs)
    return [pairs[i*24:(i+1)*24] for i in range(count)]


PI = interval(F(314159265358979323846, 10**20),
              F(314159265358979323847, 10**20))
THETA = interval(F(707106781186547524400844362104, Q),
                 F(707106781186547524400844362105, Q))
SINTH = interval(F(649636939080062444129454621098, Q),
                 F(649636939080062444132, 10**21))
COSTH = interval(F(760244597075630151252, 10**21),
                 F(760244597075630151253567702555, Q))
Z = div(SINTH, THETA)
BIGK = div(mul(PI, COSTH), Z)


def main():
    started = time.monotonic()
    source = (ROOT/'StructuralGoal20261016/WindowJetTableData.lean').read_text(encoding='utf8')
    k = parse_rows(source, 'kValues', 33)
    base = parse_rows(source, 'baseValues', 66)
    params_path = ROOT/'research-20261016-followup/window_reweight_rational.json'
    params = json.loads(params_path.read_bytes())
    numerator = params['window_coefficient_numerators_1e9']
    newwindows = (ROOT/'StructuralW10Followup20261016/NewWindows.lean').read_text(encoding='utf8')
    nums_block = newwindows.split('def nums24 :', 1)[1].split('def c24', 1)[0]
    lean_nums = [int(v) for _, v in re.findall(r'\| (\d+) => (-?\d+)', nums_block)]
    assert numerator == lean_nums and len(numerator) == 24
    D = F(sum(map(abs, numerator)), 10**9)
    assert D == F(78742791, 10**9)
    M24 = D*F(PI[1], Q)**24/(25*F(Z[0], Q))
    c = {n: [sub(k[n][r], div(add(base[2*n][r], base[2*n+1][r]), scale(Z, 2)))
             for r in range(24)] for n in range(1, 33)}
    remainders = {}

    def amplitudes(lu, uu):
        lo, hi = F(lu, SC), F(uu, SC)
        assert F(123, 128) <= lo <= hi
        n = down((lo+hi)/2 + F(1, 2))
        assert 1 <= n <= 32
        radius = max(abs(lo-n), abs(hi-n))
        assert radius <= F(1, 2)
        radius_units = radius*SC
        assert radius_units.denominator == 1
        remainders[str(radius_units.numerator)] = {
            'radius_units': radius_units.numerator, 'radius': str(radius),
            'C_error': str(M24*radius**24/factorial(24)),
            'Cprime_error': str(M24*radius**23/factorial(23))}
        delta = interval(lo-n, hi-n)
        cv = expand(polynomial(c[n], delta), M24*radius**24/factorial(24))
        cp = expand(polynomial([scale(c[n][r+1], r+1) for r in range(23)], delta),
                    M24*radius**23/factorial(23))
        x = interval(lo, hi)
        px2 = mul(square(PI), square(x))
        den = sub(px2, interval(F(1, 2)))
        assert den[0] > 0
        a = div(mul(BIGK, x), den)
        ap = div(neg(mul(BIGK, add(px2, interval(F(1, 2))))), square(den))
        b = div(neg(interval(F(1, 2))), den)
        bp = div(mul(square(PI), x), square(den))
        return n, radius_units.numerator, (a, b, cv, ap, bp, cp)

    def alpha(v):
        a, b, cv, ap, bp, cp = v
        return (
            add(add(mul(scale(cv, 2), cp), mul(a, ap)), mul(b, bp)),
            add(scale(add(mul(cp, b), mul(cv, bp)), 2), mul(mul(scale(PI, 2), cv), a)),
            sub(scale(add(mul(cp, a), mul(cv, ap)), 2), mul(mul(scale(PI, 2), cv), b)),
            add(sub(mul(b, bp), mul(a, ap)), mul(mul(scale(PI, 2), a), b)),
            sub(add(mul(ap, b), mul(a, bp)), mul(PI, sub(square(b), square(a)))))

    packed_path = HERE/'cover-curvature-parent64.input.json.gz'
    selection_path = HERE/'cover-lifted-graph-energy8.json'
    packed = packed_path.read_bytes()
    cases = {r['path']: r for r in json.loads(gzip.decompress(packed))['cases']}
    selection = json.loads(selection_path.read_bytes())
    assert selection['receipt']['input_sha256'] == sha(packed)
    pairs = [(i, i+1) for i in range(9)]
    pairs += [(i, j) for i in range(10) for j in range(i+1, 10) if j-i != 1]
    assert len(pairs) == len(set(pairs)) == 45
    terms = [(i, j, a) for i, j, a in params['a_upper'] if a > 0]
    assert len(terms) == 41
    case_receipts = []
    total_pieces = 0
    for case_index in (0, 1):
        packet_path = HERE/f'window_phase_coefficients_case{case_index}.json'
        packet = json.loads(packet_path.read_bytes())
        assert (packet['SC'], packet['DS'], packet['scale'], packet['arithmetic_scale']) == (SC, DS, DS, Q)
        assert packet['parameters_sha256'] == sha(params_path.read_bytes())
        assert packet['input_sha256'] == sha(packed)
        assert packet['selection_sha256'] == sha(selection_path.read_bytes())
        assert packet['source_sha256'] == sha((HERE/'window_phase_coefficients.py').read_bytes())
        for entry in packet['inputs']:
            assert sha((ROOT/entry['path']).read_bytes()) == entry['sha256'], entry['path']
        for name, value in [('pi', PI), ('theta', THETA), ('sin_theta', SINTH), ('cos_theta', COSTH), ('Z', Z)]:
            assert list(map(F, packet['elementary_inputs'][name])) == [F(z, Q) for z in value]
        assert F(packet['analytic_basis']['D']) == D
        assert F(packet['analytic_basis']['C24_uniform_rational_upper']) == M24
        case = packet['cases'][0]
        path = selection['rows'][case_index]['path']
        assert case['case_index'] == case_index and case['path'] == path
        state = cases[path]['before']
        assert case['cell'] == state
        assert len(case['terms']) == 41
        remainders.clear()
        case_pieces = 0
        centers = set()
        for t, ((i, j, weight), row) in enumerate(zip(terms, case['terms'])):
            assert (row['t'], row['i'], row['j'], row['weight_numerator']) == (t, i, j, weight)
            ix = pairs.index((i, j))
            lu, uu = state[0][ix], state[1][ix]
            assert [row['l_units'], row['u_units']] == [lu, uu]
            assert [F(row['l']), F(row['u'])] == [F(lu, SC), F(uu, SC)]
            cuts = sorted({lu, uu, *range((lu//1024+1)*1024, uu, 1024)})
            if lu == uu:
                cuts = [lu, uu]
            assert cuts[0] == lu and cuts[-1] == uu
            pieces, av, hv = [], [], []
            digest = hashlib.sha256()
            for l, u in zip(cuts, cuts[1:]):
                assert 0 <= u-l <= 1024
                n, ru, amps = amplitudes(l, u)
                centers.add(n)
                alphas = alpha(amps)
                piece = [l, u, n, ru]
                pieces.append(piece)
                av.append(amps)
                hv.append(alphas)
                digest.update(canon({'piece': piece,
                    'amplitude_endpoints_Q30': amps,
                    'alpha_endpoints_Q30': alphas}))
            assert pieces == row['pieces_units']
            if lu != uu:
                assert digest.hexdigest() == row['uniform_derivation_sha256']
            alpha_hulls = [envelope([a[r] for a in hv]) for r in range(5)]
            amp_hulls = [envelope([a[r] for a in av]) for r in range(6)]
            assert [list(v) for v in alpha_hulls] == row['prequantized_alpha_endpoints_Q30']
            assert [list(v) for v in amp_hulls] == row['amplitude_hulls_Q30']
            quantized = [quantize(v) for v in alpha_hulls]
            low, high = [v[0] for v in quantized], [v[1] for v in quantized]
            assert low == row['lower_numerators'] and high == row['upper_numerators']
            ref_units = (lu+uu)//2
            assert row['reference_x_units'] == ref_units and F(row['reference_x']) == F(ref_units, SC)
            _, _, amps = amplitudes(ref_units, ref_units)
            refs = [down(F(v[0]+v[1], 2*Q)*DS+F(1, 2)) for v in alpha(amps)]
            errors = [max(v-l, u-v) for l, u, v in zip(low, high, refs)]
            assert refs == row['reference_numerators'] and errors == row['error_numerators']
            for label, vals in [('lower', low), ('upper', high), ('reference', refs), ('error', errors)]:
                assert list(map(F, row[label])) == [F(v, DS) for v in vals]
            assert all(v-e <= lo and hi <= v+e for lo, hi, v, e in zip(low, high, refs, errors))
            case_pieces += len(pieces)
        assert packet['remainder_catalog'] == remainders
        assert packet['C_normalized_coefficient_endpoints_Q30'] == {
            str(n): [list(v) for v in c[n]] for n in centers}
        assert packet['diagnostics']['pieces'] == case_pieces
        case_receipts.append({'case_index': case_index, 'path': path,
            'packet_sha256': sha(packet_path.read_bytes()), 'terms': 41,
            'pieces': case_pieces, 'centers': sorted(centers)})
        total_pieces += case_pieces
    assert total_pieces == 1207
    result = {
        'status': 'PASS_EXACT_REPLAY_AND_PAPER_MATHEMATICAL_AUDIT',
        'scope': __doc__, 'script_sha256': sha(Path(__file__).read_bytes()),
        'cases': case_receipts, 'total_pieces': total_pieces,
        'checks': ['producer not imported', 'all source hashes',
            'actual nums24 vector', 'all Q30 coefficient and amplitude endpoints',
            'all 1207 exact contiguous 1/32 clipped pieces and centers',
            'all derivation digests', 'all DS lower/upper/reference/error endpoints',
            'complete remainder catalogs including reference radii'],
        'paper_audit': {
            'normalized_jets': 'kc=jet/r!, b=pi^r*sincMoment/r!; Base index=2*n+bool; table K is normalized actual k',
            'normalization': 'Z=K(0)=K0AM=sin(theta)/theta; C=k-KMT/Z; C_r=K_r-(Base_minus+Base_plus)/(2*Z)',
            'C24_bound': '|C^(24)| <= D*(2*pi)^24/Z * integral_-1/2^1/2 |t|^24 = D*pi^24/(25*Z)',
            'Cprime_remainder': 'Taylor of Cprime has degree22, next derivative C^(24), error M24*rho^23/23!',
            'harmonics': 'Expansion of 2*k*kprime with k=C+A*sin(pi*x)+B*cos(pi*x) agrees in all five coefficients',
            'elementary_bounds': 'Input rationals exactly match WindowIntegerJetRecipe; corresponding ordinary Lean enclosure theorems inspected; no compilation performed',
            'remaining_Lean_obligations': ['C_all decomposition and normalized Taylor subtraction bridge',
                'new perturbation-specific global C24 bound', 'uniform amplitude/harmonic packet consumer',
                'phase graph and strict exclusion bridge']},
        'lean_verified': False, 'strict_phase_exclusion_proven': False,
        'complete_global_cover': False, 'new_zero_proportion_proven': False,
        'seconds': time.monotonic()-started}
    out = HERE/'phase-coefficient-independent-replay.json'
    assert not out.exists(), 'Replay receipt is immutable; choose a new filename.'
    out.write_text(json.dumps(result, indent=2)+'\n', encoding='utf8')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
