"""One deterministic replay of previously audited integers, not a kernel evaluation."""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
import datetime, gzip, json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
NUM = 'research-goal-20261018-stageB-classification/numeric-classification.jsonl.gz'
EXC = 'research-goal-20261018-stageB-classification/exception-cells.jsonl.gz'
SRC = 'research-goal-20261018-record-source-audit/snapshot/Solution.lean'
STATIC = 'research-goal-20261018-record-overlap-static/static-receipt.json'
KAPPA = 335544320000000000
SA = 10**20
C9N = 893616123055294719

def pin(rel):
    b = (ROOT / rel).read_bytes()
    return {'path': rel, 'bytes': len(b), 'sha256': sha256(b).hexdigest()}

def main():
    inputs = [pin(p) for p in [NUM, EXC, SRC, STATIC]]
    assert inputs[0]['sha256'] == 'cad7880991a6fb319dc129290e71cc32970d205e45e84684c541d4e13822a74b'
    assert inputs[1]['sha256'] == '180c27713c0473345fd0bb3c3373168a2d79f2e4bf518d5860e1c72cfa8a1ad0'
    assert inputs[2]['sha256'] == 'f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf'
    rows = [json.loads(s) for s in gzip.decompress((ROOT / NUM).read_bytes()).splitlines()]
    cells = [json.loads(s) for s in gzip.decompress((ROOT / EXC).read_bytes()).splitlines()]
    assert len(rows) == 13046 and len(cells) == 1187
    assert len({(r['root'], r['position']) for r in rows}) == len(rows)
    ordered = sorted(rows, key=lambda r: int(r['original_margin']))
    first, second = ordered[:2]
    assert int(first['original_margin']) < int(second['original_margin'])
    assert (first['root'], first['position']) == (11, 27229)
    # Largest even debit strictly covered by the second margin. No parameter scan.
    delta_n = (int(second['original_margin']) // KAPPA) // 2
    assert delta_n == 389500523
    debit = KAPPA * 2 * delta_n
    exceptional = [r for r in rows if int(r['original_margin']) < debit]
    assert len(exceptional) == 1 and exceptional[0] == first
    cell = next(e for e in cells if (e['root'], e['position']) == (11, 27229))
    assert cell['state_sha256'] == first['state_sha256']
    assert cell['exception_id'] == 462 and cell['state']['M'] == 0
    lo, hi = cell['state']['L'], cell['state']['U']
    charts = []
    for left_rev in [False, True]:
        for right_rev in [False, True]:
            # The second prefix gap equals the first suffix gap in physical coordinates.
            upper = hi[6 if left_rev else 1]
            lower = lo[7 if right_rev else 0]
            assert upper < lower
            charts.append({'prefix_reversed': left_rev, 'suffix_reversed': right_rev,
                           'shared_gap_upper_Q': upper, 'shared_gap_lower_Q': lower,
                           'strict_integer_difference': lower - upper})
    s = json.loads((ROOT / STATIC).read_text(encoding='utf8'))
    H, B, c9 = map(F, [s['new_window_floor_H'], s['new_total_pressure_B9'], s['new_c9']])
    R = F(s['record_ratio_recovered_from_source_parameters'])
    delta, c, tau = F(delta_n, SA), F(C9N + delta_n, SA), F(C9N + 2*delta_n, SA)
    assert c9 == F(C9N, SA) and (H-B)/(1-c9) == R
    candidate = (H-B)/(1-c)
    assert 0 < delta and c < F(1,64) and candidate > R
    result = {
        'schema': 'single-exception-overlap-metadata-v1',
        'checked_UTC': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'inputs': inputs, 'rows': len(rows), 'source_exception_cells': len(cells),
        'minimum': first, 'second_minimum': second,
        'minimum_multiplicity': sum(r['original_margin'] == first['original_margin'] for r in rows),
        'delta_n': delta_n, 'delta': str(delta), 'c': str(c), 'tau': str(tau),
        'original_margin_debit': str(debit), 'exception_count': len(exceptional),
        'all_other_leaf_debits_nonnegative': True,
        'minimum_other_margin_after_debit': str(int(second['original_margin'])-debit),
        'exception': cell, 'four_orientation_conflicts': charts,
        'H': str(H), 'B9': str(B), 'record_R': str(R),
        'conditional_candidate': str(candidate), 'conditional_gain': str(candidate-R),
        'strict_comparison_cross_product': str(candidate.numerator*R.denominator-R.numerator*candidate.denominator),
        'scope': 'Exact reuse of audited numeric margins and cell bounds. No new actual kernel or coverage walk.',
        'missing': ['Lean raised sublevel localization including all cuts/reflections and root exterior',
                    'actual joint floor and summed counting instantiation',
                    'complete Comparator, ordinary Lean, nanoda and production size/time verification'],
        'new_kernel_queries': 0, 'LP_calls': 0, 'Lean_runs': 0,
        'new_unconditional_zero_proportion_proven': False, 'website_submission_ready': False,
        'script_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    assert inputs == [pin(r['path']) for r in inputs]
    with (HERE/'metadata-replay.json').open('x', encoding='utf8', newline='\n') as f:
        json.dump(result, f, indent=2, ensure_ascii=False); f.write('\n')
    print(json.dumps({k: result[k] for k in ['rows','delta_n','exception_count','record_R',
        'conditional_candidate','conditional_gain','new_unconditional_zero_proportion_proven']}))

if __name__ == '__main__':
    main()
