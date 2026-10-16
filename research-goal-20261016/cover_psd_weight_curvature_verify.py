"""Exact stdlib-only PSD-weight curvature certificate interface.

For nonnegative integer weights mu_l and integer directions d_l supported
on coordinates which the whole cell places strictly above the ORIGINAL
orthant floor, a local orthant minimum satisfies

  sum_l mu_l * d_l^T Hessian(F) d_l >= 0.

This module checks a strictly negative affine/flow upper bound for that
sum.  It imports the existing independent scalar and geometry verifier,
never a discovery oracle, optimizer, NumPy, or SciPy.  A successful replay
is finite rational arithmetic; new Lean soundness/global coverage remain
separate obligations.  No existing pinned source is modified.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import time

import cover_correlated_curvature_verify as prior

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SC, DS = prior.SC, prior.DS
KIND = 'correlated_PSD_weight_curvature'


def exact_int(value):
    """Do not silently truncate floating or rational certificate values."""
    assert isinstance(value, (int, str)) and not isinstance(value, bool)
    result = int(value)
    if isinstance(value, str):
        assert str(result) == value or (value.startswith('+') and str(result) == value[1:])
    return result


def make_checker(table):
    if isinstance(table, prior.CurvatureReplay):
        return table
    if isinstance(table, (str, Path)):
        table = json.loads(Path(table).read_bytes())
    return prior.CurvatureReplay(table)


def source_hashes():
    import cover_correlated_replay as scalar
    paths = {
        'PSD_weight_verifier': Path(__file__),
        'curvature_scalar_verifier': Path(prior.__file__),
        'scalar_verifier': Path(scalar.__file__),
        'geometry_verifier': Path(prior.a.__file__),
    }
    return {name: hashlib.sha256(path.read_bytes()).hexdigest() for name, path in paths.items()}


def normalize_directions(state, weighted_directions):
    """Return (mu,d) tuples; every positive-weight support is free in this cell.

    Different directions may have different supports.  Their union must be
    in I(cell)={r: lower_adjacent_gap[r]>123*SC/128}.  No condition is imposed
    at artificial upper/lower cell faces: only the original orthant matters.
    """
    assert len(state) == 2 and all(len(row) == 45 for row in state)
    assert len(weighted_directions) > 0
    sep = 123*SC//128
    result = []
    for entry in weighted_directions:
        assert set(entry) == {'weight', 'direction'}
        weight = exact_int(entry['weight'])
        direction = tuple(map(exact_int, entry['direction']))
        assert weight >= 0 and len(direction) == 9
        if not weight:
            continue
        assert any(direction)
        assert all(not d or state[0][r] > sep for r, d in enumerate(direction)), \
            'Every positive-weight direction needs common original-orthant interior support.'
        result.append((weight, direction))
    assert result, 'The PSD weight must be nonzero.'
    return tuple(result)


def expand(state, weighted_directions, scalar_affine_data, params, checker):
    """Recheck old scalar packets and form the new summed integer coefficients.

    The only new coefficients are
      q_t = a_t sum_l mu_l (sum_{r in span_t} d_l[r])^2.
    With x_t=sum gap_r, prior scalar packets certify
      DS*w''(x_t) <= m0_t+m1_t*(x_t-P_t/(2*SC))+err_t.
    Return the numerator C+E+sum coeff_r*(SC*gap_r), with the
    unchanged denominator 2*SC*parameter_denominator*DS.
    """
    checker = make_checker(checker)
    prior.a.closure_valid(state)
    directions = normalize_directions(state, weighted_directions)
    terms = [tuple(map(exact_int, term)) for term in params['a_upper'] if term[2]]
    denominator = exact_int(params['denominator'])
    assert denominator == 10**10 and len(terms) == len(scalar_affine_data) == 41
    assert all(0 <= i < j <= 9 and a > 0 for i, j, a in terms)
    constant = error = 0
    coefficient = [0]*9
    q_values = []
    affine_terms = 0
    for (i, j, a), raw in zip(terms, scalar_affine_data):
        axis = prior.a.INDEX[i, j]
        P, m0, m1, err, kind = checker.check(state[0][axis], state[1][axis], raw)
        q = a*sum(mu*sum(d[i:j])**2 for mu, d in directions)
        assert q >= 0
        q_values.append(q)
        constant += q*(2*SC*m0-m1*P)
        error += 2*SC*q*err
        for r in range(i, j):
            coefficient[r] += 2*q*m1
        affine_terms += kind == 'affine'
    return {
        'span_quadratic_weights': q_values,
        'constant': constant,
        'error': error,
        'coefficient': coefficient,
        'denominator': 2*SC*denominator*DS,
        'positive_weight_directions': len(directions),
        'affine_terms': affine_terms,
    }


def verify(state, result, params, checker):
    """Check a supplied feasible flow witness and strict total curvature sign."""
    assert result['kind'] == KIND
    expanded = expand(state, result['weighted_directions'], result['scalar_affine_data'], params, checker)
    if 'span_quadratic_weights' in result:
        assert list(map(exact_int, result['span_quadratic_weights'])) == expanded['span_quadratic_weights']
    flow = result['exact_flow']
    for key in ['constant', 'error']:
        assert exact_int(flow[key]) == expanded[key]
    coeff = expanded['coefficient']
    assert list(map(exact_int, flow['coefficient'])) == coeff
    desired = [coeff[0]]+[coeff[r]-coeff[r-1] for r in range(1, 9)]+[-coeff[-1]]
    balance = [0]*10
    cost = 0
    for row in flow['flow']['nonzero_flow']:
        assert len(row) == 4
        i, j, amount, endpoint = map(exact_int, row)
        assert 0 <= i < 10 and 0 <= j < 10 and i != j and amount >= 0
        assert endpoint == prior.a.edge_value(state, i, j)
        balance[i] += amount
        balance[j] -= amount
        cost += amount*endpoint
    assert balance == desired == list(map(exact_int, flow['flow']['divergence']))
    assert cost == exact_int(flow['flow']['cost']) and -cost == exact_int(flow['negative_maximum'])
    upper = expanded['constant']+expanded['error']+cost
    assert upper == exact_int(result['upper_numerator']) < 0
    assert exact_int(result['denominator']) == expanded['denominator']
    return {
        'passed': True,
        'strict_integer_margin': str(-upper),
        'denominator': str(expanded['denominator']),
        'positive_weight_directions': expanded['positive_weight_directions'],
        'affine_terms': expanded['affine_terms'],
        'active_scalar_terms': sum(q > 0 for q in expanded['span_quadratic_weights']),
        'flow_edges': len(flow['flow']['nonzero_flow']),
        'new_Lean_soundness_proven': False,
        'complete_global_cover': False,
        'new_zero_proportion_proven': False,
    }


def promote_rank_one(result):
    """The old certificate embeds exactly, without changing any bound/flow."""
    assert result['kind'] == 'correlated_negative_curvature'
    return {**result, 'kind': KIND,
            'weighted_directions': [{'weight': '1', 'direction': result['direction']}]}


def load_json(path):
    raw = Path(path).read_bytes()
    return raw, json.loads(gzip.decompress(raw) if str(path).endswith('.gz') else raw)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--input', required=True, type=Path,
                    help='JSON {cases:[{path,cell,result}]} with PSD-weight certificates.')
    ap.add_argument('--parameters', type=Path,
                    default=ROOT/'research-20261016-followup/window_reweight_rational.json')
    ap.add_argument('--table', type=Path, default=HERE/'cover_newjet.json')
    ap.add_argument('--output', required=True, type=Path)
    args = ap.parse_args()
    started = time.monotonic()
    raw, document = load_json(args.input)
    params_raw, params = load_json(args.parameters)
    table_raw, table = load_json(args.table)
    checker = make_checker(table)
    rows = [{'path': case['path'], **verify(case['cell'], case['result'], params, checker)}
            for case in document['cases']]
    assert rows
    receipt = {
        'scope': __doc__, 'source_sha256': source_hashes(),
        'input_sha256': hashlib.sha256(raw).hexdigest(),
        'parameters_sha256': hashlib.sha256(params_raw).hexdigest(),
        'table_sha256': hashlib.sha256(table_raw).hexdigest(),
        'all_passed': True, 'cases': len(rows), 'verified': rows,
        'new_Lean_soundness_proven': False, 'complete_global_cover': False,
        'new_zero_proportion_proven': False, 'seconds': time.monotonic()-started,
    }
    args.output.write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf8')
    print(json.dumps({k: v for k, v in receipt.items() if k not in ['scope', 'verified']}), flush=True)


if __name__ == '__main__':
    main()
