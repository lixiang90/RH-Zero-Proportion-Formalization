"""Stdlib Fraction sparse rows and outward integerization for moment RLT.

No optimizer, numerical library, or producer is imported. Old integer rows
and their scalar/geometry soundness are inputs to this algebra interface.
Row order matches the base moment model, followed by quadratic energy rows.
Finite boxes justify every rounding payment and the final aggregate check.
"""
from fractions import Fraction as F

SC = 32768
DS = 10**15
D = 10**10
Q = 2*SC*DS*D
V = 464
PAIRS = [(s, r) for s in range(9) for r in range(s, 9)]
HI = {pair: 50+k for k, pair in enumerate(PAIRS)}


def integer(value):
    assert isinstance(value, (int, str)) and not isinstance(value, bool)
    result = int(value)
    assert not isinstance(value, str) or str(result) == value
    return result


def hindex(s, r): return HI[min(s, r), max(s, r)]
def qindex(s, t): return 95+41*s+t


def add_coefficient(row, index, value):
    value = row.get(index, F(0))+F(value)
    if value:
        row[index] = value
    else:
        row.pop(index, None)


def inputs(state, old_integer_rows, old_meta, u_lower_upper, energy_packets,
           *, row_denominator=Q, tight_bounds=True):
    """Return {rows,bounds,center,radius} using exact rational arithmetic.

    Each old row is (nine gap integer coefficients, 41 scalar integer
    coefficients, integer RHS), all divided by row_denominator. The input
    old rows already have zero KKT residual: the nine soft residual variables
    of the discovery LP are not retained. Each output row is
      {'coeff': {variable_index: Fraction}, 'bound': Fraction, 'meta': ...}.
    """
    assert len(state) == 2 and all(len(r) == 45 for r in state)
    assert len(old_integer_rows) == len(old_meta) and len(u_lower_upper) == 41
    denominator = integer(row_denominator)
    assert denominator > 0
    lower = [F(integer(x), SC) for x in state[0][:9]]
    upper = [F(integer(x), SC) for x in state[1][:9]]
    center = [(a+b)/2 for a, b in zip(lower, upper)]
    radius = [(b-a)/2 for a, b in zip(lower, upper)]
    assert all(r > 0 for r in radius)
    ubounds = [tuple(map(F, pair)) for pair in u_lower_upper]
    assert all(len(pair) == 2 and -7 <= pair[0] <= pair[1] <= 7 for pair in ubounds)
    rows = []
    def append(row, bound, meta):
        assert all(isinstance(i, int) and 0 <= i < V for i in row)
        bound = F(bound)
        scale = max([F(1), abs(bound)]+[abs(value) for value in row.values()])
        rows.append({'coeff': row, 'bound': bound, 'meta': meta, 'scale': scale})
    def yadd(row, s, coefficient):
        coefficient = F(coefficient)
        add_coefficient(row, s, coefficient/radius[s])
        return coefficient*center[s]/radius[s]
    for n, ((ag, au, B), meta) in enumerate(zip(old_integer_rows, old_meta)):
        assert len(ag) == 9 and len(au) == 41
        ag = [F(integer(v), denominator) for v in ag]
        au = [F(integer(v), denominator) for v in au]
        B = F(integer(B), denominator)
        base = {i: v for i, v in enumerate(ag+au) if v}
        append(base, B, ['base', n, meta])
        K = sum(a*c for a, c in zip(ag, center))-B
        for s in range(9):
            for sign in [-1, 1]:
                row = dict(base)
                bound = B+yadd(row, s, sign*K)
                for r, a in enumerate(ag):
                    add_coefficient(row, hindex(s, r), sign*a*radius[r])
                for t, a in enumerate(au):
                    add_coefficient(row, qindex(s, t), sign*a)
                append(row, bound, ['RLT', n, s, sign, meta])
    for s, r in PAIRS:
        for a, b, sign in [(-1, -1, -1), (1, 1, -1), (-1, 1, 1), (1, -1, 1)]:
            row = {hindex(s, r): F(sign)}
            bound = F(-sign*a*b)
            bound += yadd(row, s, -sign*b)+yadd(row, r, -sign*a)
            append(row, bound, ['moment_McCormick', s, r, a, b, sign])
    for t, (L, U) in enumerate(ubounds):
        for s in range(9):
            for a, b, sign in [(-1, L, -1), (1, U, -1), (-1, U, 1), (1, L, 1)]:
                row = {qindex(s, t): F(sign)}
                add_coefficient(row, 9+t, -sign*a)
                bound = -sign*a*b+yadd(row, s, -sign*b)
                append(row, bound, ['cross_McCormick', t, s, a, str(b), sign])
    for n, packet in enumerate(energy_packets):
        row = {}
        for i, value in packet['row']:
            assert isinstance(i, int) and i not in row and 0 <= i < V and F(value)
            row[i] = F(value)
        append(row, F(packet['bound']), ['energy', n])
    # Tight scalar boxes are proved by the independent scalar graph input.
    # Their product bounds need only |y|<=1, not rank-one moment equality.
    bounds = list(zip(lower, upper))+(ubounds if tight_bounds else [(F(-7), F(7)) for _ in range(41)])
    bounds += [(F(0), F(1)) if s == r else (F(-1), F(1)) for s, r in PAIRS]
    bounds += [(-max(abs(l), abs(u)), max(abs(l), abs(u))) if tight_bounds else (F(-7), F(7))
               for _ in range(9) for l, u in ubounds]
    assert len(bounds) == V
    box_denominator = SC*DS
    scaled_bounds = [(l*box_denominator, u*box_denominator) for l, u in bounds]
    integer_bounds = [(int(l), int(u)) for l, u in scaled_bounds] if all(l.denominator == u.denominator == 1 for l, u in scaled_bounds) else None
    return {'rows': rows, 'bounds': bounds, 'center': center, 'radius': radius,
            'McCormick_u_bounds': ubounds,
            'tight_bounds': bool(tight_bounds), 'box_denominator': box_denominator,
            'integer_bounds': integer_bounds,
            'old_row_soundness_is_input': True, 'energy_packet_soundness_is_input': True}


build = inputs


def box_rows(bounds):
    """Optional explicit bound inequalities for bound-dual Farkas weights."""
    rows = []
    assert len(bounds) == V
    for i, (l, u) in enumerate(bounds):
        l, u = F(l), F(u)
        assert l <= u
        rows += [{'coeff': {i: F(1)}, 'bound': u, 'meta': ['box', i, 1]},
                 {'coeff': {i: F(-1)}, 'bound': -l, 'meta': ['box', i, -1]}]
    return rows


def integerize(row, bounds, denominator=10**30):
    """Round coefficients to integers; enlarge RHS using the finite box.

    If a.X<=B then round(N*a).X <=
      ceil(N*(B+sum |a-round(N*a)/N|*max(|lower|,|upper|))).
    Thus every output integer row is valid on the same box, even when its
    coefficients cannot be represented on the chosen common grid exactly.
    """
    denominator = integer(denominator)
    assert denominator > 0 and len(bounds) == V
    coefficient = {}
    payment = F(0)
    for i, value in row['coeff'].items():
        assert isinstance(i, int) and 0 <= i < V
        value = F(value)
        rounded = round(value*denominator)
        if rounded:
            coefficient[i] = rounded
        l, u = map(F, bounds[i])
        assert l <= u
        payment += abs(value-F(rounded, denominator))*max(abs(l), abs(u))
    exact_rhs = denominator*(F(row['bound'])+payment)
    rhs = -((-exact_rhs.numerator)//exact_rhs.denominator)
    assert F(rhs, denominator)-F(row['bound']) >= payment >= 0
    return {'coeff': coefficient, 'bound': rhs, 'denominator': denominator,
            'rounding_payment': payment, 'meta': row['meta']}


def verify_aggregate(integer_rows, weighted_rows, bounds):
    """Check a sparse nonnegative integer Farkas sum with residual box cost.

    weighted_rows is [(row_index,positive_integer_weight),...]. Duplicate
    indices are allowed and simply add. If returned strict_margin>0, the
    selected rounded inequalities and finite boxes have no common point.
    """
    assert len(bounds) == V and weighted_rows
    coefficient = {}
    bound = 0
    denominator = None
    for index, raw_weight in weighted_rows:
        assert isinstance(index, int) and 0 <= index < len(integer_rows)
        weight = integer(raw_weight)
        assert weight > 0
        row = integer_rows[index]
        if denominator is None:
            denominator = integer(row['denominator'])
        assert integer(row['denominator']) == denominator
        bound += weight*integer(row['bound'])
        for i, value in row['coeff'].items():
            add_coefficient(coefficient, i, weight*integer(value))
    minimum = sum(a*F(bounds[i][0] if a >= 0 else bounds[i][1]) for i, a in coefficient.items())
    margin = minimum-bound
    return {'coefficient': {i: int(a) for i, a in coefficient.items()},
            'bound': bound, 'box_minimum': minimum, 'strict_margin': margin,
            'strict_exclusion': margin > 0, 'denominator': denominator,
            'input_row_soundness_verified_here': False,
            'complete_global_cover': False, 'new_zero_proportion_proven': False}
