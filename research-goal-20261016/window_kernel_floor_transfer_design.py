"""Static exact audit of affine, edgewise transfer from the old nine-point floor.

No optimizer or Lean invocation.  The rational sign brackets prove the existence
of nine new-kernel roots, subject only to the displayed sinc-integral identity,
continuity, and the standard Machin/Taylor interval facts.  The resulting upper
bound concerns one specified transfer-certificate class, never the true minimum.
"""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal, localcontext
import ast, hashlib, json, re, sys, time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
INTERVAL = ROOT/'research-20261016-followup/global_periodic_upper_bound.py'
sys.path.insert(0, str(INTERVAL.parent))
import global_periodic_upper_bound as iv

PARAM = ROOT/'research-20261016-followup/window_reweight_rational.json'
LOCAL = ROOT/'GramDefect20261015/Core.lean'
FINAL = ROOT/'GramDefect20261015/Final.lean'
SITE = ROOT/'research-20261016-w10-cert/current-record-source.txt'
REVIEW = ROOT/'research-20261016-w10-cert/current-record-review.json'
SUBMISSION = ROOT/'research-20261016-w10-cert/website-snapshot/submissions/attempt-024/submission.json'
S = F(123, 128)
C = F(11, 10)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def decimal(x):
    with localcontext() as ctx:
        ctx.prec = 35
        return str(Decimal(x.numerator)/Decimal(x.denominator))


def parse_old(path):
    text = path.read_text(encoding='utf8')
    def integer(name):
        return int(re.search(r'^def '+name+r' : ℕ := (\d+)\s*$', text, re.M)[1])
    def literal(name):
        return ast.literal_eval(re.search(r'^def '+name+r' : List[^\n]* := (\[[^\n]*\])\s*$', text, re.M)[1])
    scale = integer('SA')
    pressure = [F(n, scale) for n in literal('BS')]
    terms = {(i, j): F(a, scale) for i, j, a, _ in literal('TS')}
    coeff_text = re.search(r'^def cAMn[^\n]*\n(.*?)^def cAM ', text, re.M | re.S)[1]
    coeff = {int(i): int(n) for i, n in re.findall(r'\| (\d+) => (-?\d+)', coeff_text)}
    assert len(pressure) == 8 and len(terms) == 34 and len(coeff) == 13
    domain = re.search(r'^theorem cert_AM :[^\n]+', text, re.M)[0]
    assert '∀ g : Fin 8 → ℝ, (∀ i, 0 ≤ g i) →' in domain
    return {'c': F(integer('cN'), scale), 'b': pressure, 'a': terms,
            'coeff': coeff, 'floor_theorem_statement': domain}


def amplitude(point, coeff):
    """Same exact finite sinc sum as the normalized cosine-profile transform.

    No evaluation is made at an integer perturbation pole.  The two base terms
    equal (sinc(pi*x+sqrt(2)/2)+sinc(pi*x-sqrt(2)/2))/2.
    """
    x = F(point)
    px = iv.PI*x
    sx = iv.sin_interval(px)
    k = iv.sin_interval(px+iv.SQRT2/2)/(2*px+iv.SQRT2)
    k += iv.sin_interval(px-iv.SQRT2/2)/(2*px-iv.SQRT2)
    for j, n in enumerate(coeff, 1):
        assert x*x != j*j
        k += F(n, 10**9)*((-1)**j)*sx*x/(iv.PI*(x*x-j*j))
    return k/iv.NORMAL


def signs(coeff):
    rows = []
    for rank in range(1, 10):
        left = max(rank*S, F(rank)-F(1, 10))
        right = F(rank)+F(1, 10)
        a, b = amplitude(left, coeff), amplitude(right, coeff)
        assert (a.l > 0 and b.u < 0) or (a.u < 0 and b.l > 0), rank
        assert rank*S <= left < right <= C*rank
        rows.append({'rank': rank, 'left': str(left), 'right': str(right),
                     'amplitude_left_interval': [str(a.l), str(a.u)],
                     'amplitude_right_interval': [str(b.l), str(b.u)],
                     'root_exists_by_IVT': True})
    return rows


def embeddings(old, new):
    out = []
    for deleted in range(10):
        vertices = [i for i in range(10) if i != deleted]
        b = [F(0) for _ in range(9)]
        a = {}
        for r in range(8):
            for v in range(vertices[r], vertices[r+1]):
                b[v] += old['b'][r]
        for (i, j), weight in old['a'].items():
            a[vertices[i], vertices[j]] = weight
        assert b[4] == old['b'][3] == old['b'][4]
        assert sum(b) >= sum(old['b'])
        holes = [[i, j, str(weight)] for (i, j), weight in a.items()
                 if weight and not new[i, j]]
        assert holes  # No single deletion embeds coefficientwise into new a.
        out.append({'deleted_vertex': deleted, 'vertices': vertices,
                    'embedded_b': list(map(str, b)),
                    'pressure_sum': str(sum(b)),
                    'positive_old_edges_at_zero_new_weight': holes})
    return out


def bound(old, params, label):
    bnew = [F(n, params['denominator']) for n in params['b_numerators']]
    anew = {(i, j): F(n, params['denominator']) for i, j, n in params['a_upper']}
    em = embeddings(old, anew)
    alpha_cap = bnew[4]/old['b'][3]
    assert old['c']-C*sum(old['b']) > 0
    upper = C*sum(bnew)+alpha_cap*(old['c']-C*sum(old['b']))
    h = F(params['window_H_lower'])
    review = json.loads(REVIEW.read_bytes())
    record = F(review['current_record_exact'])
    required = 1-(h-sum(bnew))/record
    assert upper < required < F(11, 1250)
    dilation_necessary = old['c']/((required-C*sum(bnew))/alpha_cap+C*sum(old['b']))
    dilation = F(24, 25)
    scaled_upper = C*sum(bnew)+alpha_cap*(old['c']/dilation-C*sum(old['b']))
    return {'source': label, 'old_local_floor': str(old['c']),
            'old_floor_theorem_statement': old['floor_theorem_statement'],
            'old_floor_requires_only_nonnegative_gaps': True,
            'old_pressure': str(sum(old['b'])),
            'old_central_pressure': str(old['b'][3]),
            'new_pressure': str(sum(bnew)), 'new_central_pressure': str(bnew[4]),
            'sum_lambda_upper': str(alpha_cap),
            'sum_lambda_upper_decimal': decimal(alpha_cap),
            'transfer_floor_upper': str(upper),
            'transfer_floor_upper_decimal': decimal(upper),
            'required_floor_to_match_archived_record': str(required),
            'required_floor_decimal': decimal(required),
            'strict_floor_shortfall': str(required-upper),
            'strict_floor_shortfall_decimal': decimal(required-upper),
            'counting_formula_at_transfer_upper_percent': decimal(100*(h-sum(bnew))/(1-upper)),
            'optimistic_dilation_necessary_t_upper': str(dilation_necessary),
            'optimistic_dilation_necessary_t_upper_decimal': decimal(dilation_necessary),
            'static_dilation_24_over_25': {
                'r': str(dilation), 'r_times_new_SEP': str(dilation*S),
                'old_floor_domain_satisfied': True,
                'no_scaled_kernel_counting_admissibility_claim': True,
                'optimistic_transfer_upper': str(scaled_upper),
                'optimistic_transfer_upper_decimal': decimal(scaled_upper),
                'uniform_kernel_comparison_established': False,
            },
            'embeddings': em}


def main():
    started = time.monotonic()
    paths = [Path(__file__), PARAM, LOCAL, FINAL, SITE, REVIEW, SUBMISSION, INTERVAL]
    before = {str(p.relative_to(ROOT)).replace('\\', '/'): sha(p) for p in paths}
    params = json.loads(PARAM.read_bytes())
    local, site = parse_old(LOCAL), parse_old(SITE)
    review = json.loads(REVIEW.read_bytes())
    assert review['frozen_core_sha256'] == sha(LOCAL)
    assert review['record_source_sha256'] == sha(SITE)
    assert all(row['byte_identical'] for row in review['kernel_definition_checks'])
    assert local['coeff'] == site['coeff']
    assert local['c'] == F(859538525913875481, 10**20)
    assert sum(local['b']) == F(437688, 10**8)
    assert sum(site['b']) == F(437542, 10**8)
    roots = signs(params['window_coefficient_numerators_1e9'])
    checks = [bound(local, params, 'locally formalized RiemannFail.cert_AM imported by GramDefect20261015/Final.lean'),
              bound(site, params, 'archived accepted attempt-024; no new local Lean replay')]
    mixed_upper = max(F(row['transfer_floor_upper']) for row in checks)
    after = {str(p.relative_to(ROOT)).replace('\\', '/'): sha(p) for p in paths}
    assert before == after
    result = {
        'scope': __doc__,
        'certificate_class': 'Nonnegative combinations of unscaled old 9-point delete-one embeddings, univariate affine edge minorants on unbounded rank-separated domains, and nonnegative coordinate pressure residue.',
        'separation': str(S), 'root_ratio_upper': str(C),
        'analytic_inputs': [
            'The displayed finite sinc sum equals the actual normalized Fourier transform.',
            'Continuity and the intermediate value theorem.',
            'Machin identity, alternating atan enclosure, sin Taylor remainder, and integer-square-root enclosure.',
            'Both finite sinc-square kernels tend to zero at infinity and are nonnegative.'
        ],
        'root_brackets': roots, 'bounds': checks,
        'mixed_two_old_families_transfer_upper': str(mixed_upper),
        'mixed_two_old_families_transfer_upper_decimal': decimal(mixed_upper),
        'source_sha256': before, 'sources_unchanged': True,
        'proof_status': 'Exact rational interval and algebra audit; no optimizer, no Lean invocation, not a new zeta bound.',
        'does_not_exclude': [
            'Scaled old configurations, e.g. w_old(t*x) and t*b_old.',
            'Compact sublevel-domain comparisons with additional global pressure constraints.',
            'Coupled multi-span inequalities, nonlinear potentials, or a new old-floor theorem.'
        ],
        'elapsed_seconds_hint': decimal(F(str(time.monotonic()-started)))
    }
    target = HERE/'window-kernel-floor-transfer-design.json'
    target.write_text(json.dumps(result, indent=2, allow_nan=False)+'\n', encoding='utf8')
    print(json.dumps({'root_brackets': len(roots), 'checks': [{k: v for k, v in row.items() if k != 'embeddings'} for row in checks], 'sources_unchanged': True}, indent=2))


if __name__ == '__main__':
    if not __debug__: raise RuntimeError('Assertions must remain enabled')
    main()
