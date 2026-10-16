"""Stdlib replay of the fixed two-cell finite PSD-weight curvature search.

Recheck every selected weight, scalar packet, summed coefficient, DBM flow,
and final upper bound independently of the producer. A nonnegative upper
bound is recorded as no exclusion, never as a feasibility theorem.
"""
from pathlib import Path
from fractions import Fraction as F
import gzip
import hashlib
import json
import time
import cover_psd_weight_curvature_verify as v
import cover_contractor_verify as flow_checker

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sha = lambda raw: hashlib.sha256(raw).hexdigest()


def main():
    started = time.monotonic()
    raw = (HERE/'cover-psd-weight-curvature-two.json').read_bytes()
    document = json.loads(raw)
    cell_raw = (HERE/'cover-curvature-parent64.input.json.gz').read_bytes()
    cells = {c['path']: c for c in json.loads(gzip.decompress(cell_raw))['cases']}
    table_raw = (HERE/'cover_newjet.json').read_bytes()
    params_raw = (ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes()
    params = json.loads(params_raw)
    checker = v.make_checker(json.loads(table_raw))
    rows = []
    for row in document['rows']:
        state = row['cell']
        assert state == cells[row['path']]['before']
        candidate = row['candidate']
        assert candidate['kind'] == v.KIND
        expanded = v.expand(state, candidate['weighted_directions'], candidate['scalar_affine_data'], params, checker)
        flow = candidate['exact_flow']
        for key in ['constant', 'error']:
            assert int(flow[key]) == expanded[key]
        assert list(map(int, flow['coefficient'])) == expanded['coefficient']
        minimum = flow_checker.flow_bound(state, [-a for a in expanded['coefficient']], flow['flow'])
        assert minimum == int(flow['negative_maximum'])
        upper = expanded['constant']+expanded['error']-minimum
        assert upper == int(candidate['upper_numerator'])
        assert int(candidate['denominator']) == expanded['denominator']
        strict = v.verify(state, candidate, params, checker) if upper < 0 else None
        rows.append({'path': row['path'], 'all_finite_checks_passed': True,
                     'positive_weight_directions': expanded['positive_weight_directions'],
                     'upper_numerator': str(upper), 'denominator': str(expanded['denominator']),
                     'normalized_upper_per_direction_weight': str(F(upper, expanded['denominator']*sum(int(d['weight']) for d in candidate['weighted_directions']))),
                     'strict_exclusion': upper < 0, 'strict_receipt': strict,
                     'nonnegative_upper_is_not_a_feasibility_proof': True})
    assert len(rows) == 2
    out = {'scope': __doc__, 'script_sha256': sha(Path(__file__).read_bytes()),
           'input_sha256': sha(raw), 'cell_input_sha256': sha(cell_raw),
           'table_sha256': sha(table_raw), 'parameters_sha256': sha(params_raw),
           'verifier_sources_sha256': v.source_hashes(),
           'flow_checker_sha256': sha(Path(flow_checker.__file__).read_bytes()),
           'all_finite_checks_passed': True, 'cases': rows,
           'strict_exclusions': sum(r['strict_exclusion'] for r in rows),
           'PSD_weight_Lean_consumer_proven': False, 'complete_global_cover': False,
           'new_zero_proportion_proven': False, 'seconds': time.monotonic()-started}
    output = HERE/'cover-psd-weight-curvature-replay.json'
    output.write_text(json.dumps(out, indent=2)+'\n', encoding='utf8')
    print(json.dumps({'all_finite_checks_passed': True, 'cases': len(rows),
                      'strict_exclusions': out['strict_exclusions'], 'seconds': out['seconds'],
                      'receipt_sha256': sha(output.read_bytes())}), flush=True)


if __name__ == '__main__':
    main()
