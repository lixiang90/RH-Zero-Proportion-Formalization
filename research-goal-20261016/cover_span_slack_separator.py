"""Exact DBM/sublevel affine factors and a bounded floating separator.

No optimizer is imported.  Only ``select`` imports NumPy.  A selection is
discovery, not a certificate: the integer old atom and exact affine factor
are saved, and a later independent checker must establish their soundness.
The factors use nonadjacent DBM slacks or the single pressure sublevel
slack.  Their positivity is not inferred from the independent gap box.
"""
from fractions import Fraction as F
import heapq

SC = 32768
V = 464
PAIRS = [(s, r) for s in range(9) for r in range(s, 9)]
SPANS = [(i, i+1) for i in range(9)]+[(i, j) for i in range(9) for j in range(i+2, 10)]
HI = {p: 50+k for k, p in enumerate(PAIRS)}


def add(row, i, value):
    value = row.get(i, F(0))+F(value)
    if value:
        row[i] = value
    else:
        row.pop(i, None)


def factors(state, pressure_numerators, ledger_denominator=10**10,
            floor=F(11, 1250), sep_units=31488):
    """Return only correlation-improving nonadjacent factors, plus pressure.

    Each factor is (A_num + sum b_num[s]*y_s)/denominator.  Here
    y_s=(g_s-centre_s)/radius_s.  Span factors equal twice the corresponding
    physical span slack divided by the span width.  The pressure factor is
    2*(floor-P(g))/(floor-P(sep)).
    """
    lo, hi = state
    assert len(lo) == len(hi) == 45 and all(l <= u for l, u in zip(lo, hi))
    assert all(lo[s] < hi[s] and lo[s] >= sep_units for s in range(9))
    result = []
    for axis, (i, j) in enumerate(SPANS):
        if axis < 9:
            continue
        width = hi[axis]-lo[axis]
        if width <= 0:
            continue
        for sign in (1, -1):
            deficit = lo[axis]-sum(lo[i:j]) if sign == 1 else sum(hi[i:j])-hi[axis]
            assert deficit >= 0, 'Expected a closed DBM cell.'
            if not deficit:
                continue  # Sum of old adjacent box factors: no new cone.
            A = sum(lo[s]+hi[s] for s in range(i, j))-2*lo[axis] if sign == 1 else 2*hi[axis]-sum(lo[s]+hi[s] for s in range(i, j))
            bs = [[s, sign*(hi[s]-lo[s])] for s in range(i, j)]
            result.append({'kind': 'DBM-span-slack', 'span_axis': axis,
              'pair': [i, j], 'side': sign, 'correlation_deficit_units': deficit,
              'A_numerator': str(A), 'b_numerators': [[s, str(v)] for s, v in bs],
              'denominator': str(width)})
    bs = list(map(int, pressure_numerators));D = int(ledger_denominator)
    assert len(bs) == 9 and min(bs) > 0 and D > 0
    floor_units = F(floor)*D*SC
    assert floor_units.denominator == 1
    denominator = int(floor_units)-sep_units*sum(bs)
    assert denominator > 0
    result.append({'kind': 'pressure-sublevel-slack', 'target': str(F(floor)),
      'pressure_numerators': bs, 'ledger_denominator': str(D), 'sep_units': sep_units,
      'A_numerator': str(2*int(floor_units)-sum(b*(l+u) for b, l, u in zip(bs, lo[:9], hi[:9]))),
      'b_numerators': [[s, str(-bs[s]*(hi[s]-lo[s]))] for s in range(9)],
      'denominator': str(denominator)})
    return result


def parse_factor(factor):
    d = int(factor['denominator']);assert d > 0
    A = F(int(factor['A_numerator']), d)
    b = [F(0)]*9;seen = set()
    for s, n in factor['b_numerators']:
        assert isinstance(s, int) and 0 <= s < 9 and s not in seen
        seen.add(s);b[s] = F(int(n), d)
    return A, b


def product_row(state, old_integer_row, factor, old_atom_index, old_meta,
                denominator=2*SC*10**15*10**10):
    """Expand factor*(old affine residual) in all 464 moment coordinates."""
    lower = [F(v, SC) for v in state[0][:9]]
    upper = [F(v, SC) for v in state[1][:9]]
    center = [(l+u)/2 for l, u in zip(lower, upper)]
    radius = [(u-l)/2 for l, u in zip(lower, upper)]
    assert min(radius) > 0
    ag, au, B = old_integer_row
    assert len(ag) == 9 and len(au) == 41
    ag = [F(int(v), denominator) for v in ag]
    au = [F(int(v), denominator) for v in au];B = F(int(B), denominator)
    A, b = parse_factor(factor);K = sum(a*m for a, m in zip(ag, center))-B
    row = {s: A*a for s, a in enumerate(ag) if A*a}
    for t, a in enumerate(au):
        add(row, 9+t, A*a)
    bound = A*B
    for s in range(9):
        add(row, s, b[s]*K/radius[s]);bound += b[s]*K*center[s]/radius[s]
        for r in range(9):
            add(row, HI[min(s, r), max(s, r)], b[s]*ag[r]*radius[r])
        for t in range(41):
            add(row, 95+41*s+t, b[s]*au[t])
    scale = max([F(1), abs(bound)]+[abs(v) for v in row.values()])
    return {'coeff': row, 'bound': bound, 'scale': scale,
      'meta': ['affine-slack-RLT', int(old_atom_index), old_meta, factor]}


def select(state, old_integer_rows, old_meta, primal, candidates, *,
           limit=64, excluded=(), row_denominator=2*SC*10**15*10**10):
    """Select at most64 most violated scale-normalized rows, no dense model.

    The scores are floating hints. Exact rows are constructed only for the
    selected pairs.  Working arrays have shape <=number_of_factors*45,
    rather than number_of_old_atoms*number_of_factors*464.
    """
    import numpy as np
    assert 0 < limit <= 64 and len(primal) == V
    assert len(old_integer_rows) == len(old_meta)
    excluded = set(map(tuple, excluded));heap = []
    x = np.asarray(primal, dtype=float)
    center = (np.asarray(state[0][:9])+np.asarray(state[1][:9]))/(2*SC)
    radius = (np.asarray(state[1][:9])-np.asarray(state[0][:9]))/(2*SC)
    assert min(radius) > 0
    ys = (x[:9]-center)/radius
    H = np.zeros((9, 9))
    for s, r in PAIRS:
        H[s, r] = H[r, s] = x[HI[s, r]]
    Qm = x[95:].reshape(9, 41)
    parsed = [parse_factor(f) for f in candidates]
    A = np.array([float(a) for a, b in parsed]);b = np.array([[float(v) for v in bs] for a, bs in parsed])
    bmax = np.max(np.abs(b), axis=1)
    tested = 0;maximum = 0.;positive = 0
    for oldid, (agi, aui, Bi) in enumerate(old_integer_rows):
        ag = np.array([float(F(int(v), row_denominator)) for v in agi])
        au = np.array([float(F(int(v), row_denominator)) for v in aui])
        B = float(F(int(Bi), row_denominator));K = float(ag@center-B)
        residual = float(ag@x[:9]+au@x[9:50]-B)
        cross = K*ys+H@(ag*radius)+Qm@au
        raw = A*residual+b@cross
        gcoeff = A[:, None]*ag[None, :]+b*(K/radius)[None, :]
        hmax = np.zeros(len(candidates))
        for s, r in PAIRS:
            v = b[:, s]*ag[r]*radius[r]
            if r != s:
                v = v+b[:, r]*ag[s]*radius[s]
            hmax = np.maximum(hmax, np.abs(v))
        bounds = A*B+b@(K*center/radius)
        maxau = max(abs(au))
        scales = np.maximum.reduce([np.ones(len(A)), abs(bounds), np.max(abs(gcoeff), axis=1),
          abs(A)*maxau, bmax*maxau, hmax])
        scores = raw/scales
        for fi, score in enumerate(scores):
            if (oldid, fi) in excluded:
                continue
            tested += 1;maximum = max(maximum, float(score))
            if score <= 1e-10:
                continue
            positive += 1;entry = (float(score), oldid, fi, float(raw[fi]), float(scales[fi]))
            if len(heap) < limit:
                heapq.heappush(heap, entry)
            elif entry > heap[0]:
                heapq.heapreplace(heap, entry)
    selected = []
    for score, oldid, fi, raw, scale in sorted(heap, reverse=True):
        row = product_row(state, old_integer_rows[oldid], candidates[fi], oldid, old_meta[oldid], row_denominator)
        value = sum(float(v)*x[k] for k, v in row['coeff'].items())-float(row['bound'])
        assert abs(value-raw) <= 1e-8*max(1., abs(raw), float(row['scale']))
        assert abs(float(row['scale'])-scale) <= 1e-9*max(1., scale)
        selected.append({'old_atom_index': oldid, 'factor_index': fi,
          'score_hint': score, 'residual_hint': raw, 'exact_row': row})
    return selected, {'candidate_factors': len(candidates), 'candidate_products_inspected': tested,
      'positive_violation_hints': positive, 'maximum_normalized_violation_hint': maximum,
      'selected': len(selected), 'dense_all_product_matrix_materialized': False}


def serialize_row(row):
    return {'coeff': [[i, str(v)] for i, v in sorted(row['coeff'].items())],
      'bound': str(row['bound']), 'scale': str(row['scale']), 'meta': row['meta']}


def exact_identity_check(state, integer_row, factor, gaps, scalars):
    """Pure-rational factorization at one explicit rank-one lifted point."""
    assert len(gaps) == 9 and len(scalars) == 41
    center = [F(l+u, 2*SC) for l, u in zip(state[0][:9], state[1][:9])]
    radius = [F(u-l, 2*SC) for l, u in zip(state[0][:9], state[1][:9])]
    y = [(F(v)-m)/r for v, m, r in zip(gaps, center, radius)]
    point = list(map(F, gaps))+list(map(F, scalars))+[y[s]*y[r] for s, r in PAIRS]
    point += [y[s]*F(scalars[t]) for s in range(9) for t in range(41)]
    row = product_row(state, integer_row, factor, 0, ['identity-test'])
    A, b = parse_factor(factor);ag, au, B = integer_row;D = 2*SC*10**15*10**10
    old = sum(F(int(a), D)*F(v) for a, v in zip(list(ag)+list(au), list(gaps)+list(scalars)))-F(int(B), D)
    lifted = sum(v*point[i] for i, v in row['coeff'].items())-row['bound']
    assert lifted == (A+sum(a*v for a, v in zip(b, y)))*old
    return str(lifted)
