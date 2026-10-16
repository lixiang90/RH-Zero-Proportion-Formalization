"""Independent trig/corner replay of the two research phase graph cases.

The graph producer is imported only to obtain its rectangles and facets.
Enclosures are independently checked using Q90 Machin/Taylor arithmetic,
then all facet corners are checked with integer arithmetic. No Lean run.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import factorial
from pathlib import Path
import gzip
import hashlib
import json
import time
import window_phase_graph_oracle as producer

HERE = Path(__file__).resolve().parent
SC, DS, Q = 32768, 10**15, 10**90


def down(x):
    x = F(x)
    return x.numerator//x.denominator


def up(x):
    return -down(-F(x))


def iv(a, b=None):
    return down(F(a)*Q), up(F(a if b is None else b)*Q)


def add(a, b):
    return a[0]+b[0], a[1]+b[1]


def neg(a):
    return -a[1], -a[0]


def mul(a, b):
    c = [x*y for x in a for y in b]
    return min(c)//Q, -((-max(c))//Q)


def arctan_bounds(denom):
    x = F(1, denom)
    count = 170
    value = sum(((-1)**j*x**(2*j+1)/F(2*j+1) for j in range(count)), F(0))
    nxt = (-1)**count*x**(2*count+1)/F(2*count+1)
    return min(value, value+nxt), max(value, value+nxt)


a, b = arctan_bounds(5), arctan_bounds(239)
PI = iv(16*a[0]-4*b[1], 16*a[1]-4*b[0])


@lru_cache(None)
def point(x):
    x = F(x)
    q = x-2*down((x+1)/2)
    assert -1 <= q < 1
    if q in (-1, 0):
        return iv(0)
    if q in (F(-1, 2), F(1, 2)):
        return iv(2*q)
    arg = mul(PI, iv(q))
    z = mul(arg, arg)
    # Degree121 agrees with the degree122 Taylor polynomial. All 123rd
    # derivatives of sin have absolute value <= 1.
    value = iv(F((-1)**60, factorial(121)))
    for j in range(59, -1, -1):
        value = add(mul(value, z), iv(F((-1)**j, factorial(2*j+1))))
    value = mul(value, arg)
    err = up(F(22, 7)**123/factorial(123)*Q)
    return max(-Q, value[0]-err), min(Q, value[1]+err)


def bounds(lu, uu, harmonic, part):
    shift = F(1, 2) if part == 0 else F(0)
    l, u = F(lu*harmonic, SC)+shift, F(uu*harmonic, SC)+shift
    assert l <= u
    if u-l >= 2:
        return -Q, Q
    p, q = point(l), point(u)
    lower, upper = min(p[0], q[0]), max(p[1], q[1])
    for k in range(up(l-F(1, 2)), down(u-F(1, 2))+1):
        if k % 2:
            lower = -Q
        else:
            upper = Q
    return lower, upper


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    start = time.monotonic()
    packed_path = HERE/'cover-curvature-parent64.input.json.gz'
    selection_path = HERE/'cover-lifted-graph-energy8.json'
    original_path = HERE/'window-phase-graph-oracle-two.json'
    receipt = json.loads(original_path.read_bytes())
    assert sha(HERE/'window_phase_graph_oracle.py') == receipt['source_sha256']
    assert sha(packed_path) == receipt['input_sha256']
    assert sha(selection_path) == receipt['selection_sha256']
    cases = {c['path']: c for c in json.loads(gzip.decompress(packed_path.read_bytes()))['cases']}
    selected = json.loads(selection_path.read_bytes())['rows'][:2]
    oracle = producer.PhaseGraphOracle()
    summaries = []
    corner_checks = 0
    for index, selection in enumerate(selected):
        path = selection['path']
        lower, upper = cases[path]['before']
        queries = rectangles = facets = maximum = 0
        for lu, uu in zip(lower, upper):
            for harmonic in (1, 2):
                for part in (0, 1):
                    rs = oracle.rectangles(lu, uu, harmonic, part)
                    cuts = [lu]+list(range((lu//512+1)*512, uu, 512))+[uu]
                    assert [(a, b) for a, b, _, _ in rs] == list(zip(cuts, cuts[1:]))
                    for a, b, lo, hi in rs:
                        assert 0 <= b-a <= 512
                        independent_lo, independent_hi = bounds(a, b, harmonic, part)
                        assert lo*Q <= DS*independent_lo
                        assert DS*independent_hi <= hi*Q
                    rows, count = oracle.facets(lu, uu, harmonic, part)
                    assert count == len(rs)
                    for sign, slope, intercept in rows:
                        assert sign in (-1, 1) and isinstance(slope, int) and isinstance(intercept, int)
                        for a, b, lo, hi in rs:
                            vals = [SC*y-slope*x for x in (a, b) for y in (lo, hi)]
                            if sign == 1:
                                assert max(vals) <= intercept
                            else:
                                assert intercept <= min(vals)
                            corner_checks += 4
                    queries += 1
                    rectangles += count
                    facets += len(rows)
                    maximum = max(maximum, len(rows))
        summary = {'path': path, 'queries': queries, 'rectangles': rectangles,
                   'facets': facets, 'maximum_facets_per_query': maximum}
        assert summary == receipt['cases'][index]
        summaries.append(summary)
    result = {'status': 'PASS_INDEPENDENT_Q90_TRIG_AND_INTEGER_CORNER_REPLAY',
        'scope': __doc__, 'script_sha256': sha(Path(__file__)),
        'receipt_sha256': sha(original_path),
        'dependency_sha256': {p: sha(HERE/p) for p in
            ['window_phase_graph_oracle.py', 'window_interval_kernel.py']},
        'sine_dependency_sha256': sha(HERE.parent/'research-20261016-followup/global_periodic_upper_bound.py'),
        'cases': summaries, 'total_queries': sum(s['queries'] for s in summaries),
        'total_rectangles': sum(s['rectangles'] for s in summaries),
        'total_facets': sum(s['facets'] for s in summaries), 'integer_corner_checks': corner_checks,
        'independent_sine_points': point.cache_info().currsize,
        'paper_audit': 'Exact period-two reduction, all critical half-integers, clipped 1/64 cover, and SC*DS*f(x)-SC*slope*x intercept scaling are correct; arbitrary integer slopes are safe because every rectangle corner is checked.',
        'lean_verified': False, 'analytic_trig_interface_Lean_proven': False,
        'strict_phase_exclusion_proven': False, 'complete_global_cover': False,
        'new_zero_proportion_proven': False, 'seconds': time.monotonic()-start}
    output = HERE/'phase-graph-independent-replay.json'
    assert not output.exists()
    output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf8')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
