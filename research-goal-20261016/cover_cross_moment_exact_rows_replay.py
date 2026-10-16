"""Finite stdlib audit of the exact sparse moment-row interface.

Compare every row/index to the independently rationalized producer AST
on two cells and three generic dense old rows; recheck every integerization
payment and a synthetic strict Farkas contradiction. Old scalar-row
soundness and a new real-cell contradiction are not claimed here.
"""
from pathlib import Path
from fractions import Fraction as F
import gzip
import hashlib
import json
import time
import cover_cross_moment_exact_rows as exact
import cover_cross_moment_algebra_replay as algebra

HERE = Path(__file__).resolve().parent
sha = lambda raw: hashlib.sha256(raw).hexdigest()


def main():
    started = time.monotonic()
    producer_raw = (HERE/'cover_cross_moment_probe.py').read_bytes()
    cell_raw = (HERE/'cover-curvature-parent64.input.json.gz').read_bytes()
    energy_raw = (HERE/'cover-cross-moment-energy-two.json').read_bytes()
    table_raw = (HERE/'cover_newjet.json').read_bytes()
    params_raw = (HERE.parent/'research-20261016-followup/window_reweight_rational.json').read_bytes()
    cases = {c['path']: c for c in json.loads(gzip.decompress(cell_raw))['cases']}
    document = json.loads(energy_raw)
    params = json.loads(params_raw)
    terms = [tuple(t) for t in params['a_upper'] if t[2]]
    table = json.loads(table_raw)
    dense = [[F(((j+2)*(k+1)) % 13-6, 7) for j in range(50)] for k in range(3)]
    rhs = [F(-2, 3), F(5, 7), F(-1, 11)]
    old_rows = [([int(v*231) for v in row[:9]], [int(v*231) for v in row[9:]], int(B*231))
                for row, B in zip(dense, rhs)]
    results = []
    for case in document['rows']:
        state = cases[case['path']]['before']
        reference, center, radius, ref_bounds, error = algebra.row_constructor(producer_raw.decode('utf8'), terms, table, state)
        model = exact.inputs(state, old_rows, [['audit']]*3, ref_bounds[9:50], case['energy_packets'], row_denominator=231)
        assert model['center'] == list(center) and model['radius'] == list(radius) and error == 0
        assert len(model['rows']) == len(reference)+2
        for row, (coeff, bound, kind) in zip(model['rows'], reference):
            sparse = {i: value for i, value in enumerate(coeff) if value}
            assert row['coeff'] == sparse and row['bound'] == bound
            assert row['scale'] == max([F(1), abs(bound)]+[abs(a) for a in sparse.values()])
        for row, packet in zip(model['rows'][-2:], case['energy_packets']):
            assert row['coeff'] == {i: F(value) for i, value in packet['row']}
            assert row['bound'] == F(packet['bound'])
        integer_rows = [exact.integerize(row, model['bounds']) for row in model['rows']]
        for row, converted in zip(model['rows'], integer_rows):
            N = converted['denominator']
            difference = {i: F(converted['coeff'].get(i, 0))-N*a for i, a in row['coeff'].items()}
            maximum = sum(a*F(model['bounds'][i][1] if a >= 0 else model['bounds'][i][0]) for i, a in difference.items())
            assert maximum <= converted['bound']-N*row['bound']
        # Deliberately contradictory synthetic pair: x<=m-r/2 and
        # x>=m+r/2. It checks aggregation, not any actual cell inequality.
        m, r = model['center'][0], model['radius'][0]
        test_rows = [{'coeff': {0: F(1)}, 'bound': m-r/2, 'meta': ['synthetic', 0]},
                     {'coeff': {0: F(-1)}, 'bound': -m-r/2, 'meta': ['synthetic', 1]}]
        test_int = [exact.integerize(row, model['bounds']) for row in test_rows]
        check = exact.verify_aggregate(test_int, [(0, '1'), (1, '1')], model['bounds'])
        assert check['strict_exclusion'] and not check['coefficient']
        results.append({'path': case['path'], 'generic_dense_old_rows': 3,
                        'producer_rows_compared': len(reference), 'energy_rows_compared': 2,
                        'outward_integerization_box_checks': len(integer_rows),
                        'synthetic_strict_aggregate_passed': True})
    receipt = {'scope': __doc__, 'script_sha256': sha(Path(__file__).read_bytes()),
               'exact_interface_sha256': sha(Path(exact.__file__).read_bytes()),
               'rationalized_AST_helper_sha256': sha(Path(algebra.__file__).read_bytes()),
               'producer_sha256': sha(producer_raw), 'cell_input_sha256': sha(cell_raw),
               'energy_input_sha256': sha(energy_raw), 'table_sha256': sha(table_raw),
               'parameters_sha256': sha(params_raw), 'all_checks_passed': True, 'cases': results,
               'actual_old_row_soundness_reproved': False, 'real_cell_strict_certificates': 0,
               'new_Lean_consumer_proven': False, 'complete_global_cover': False,
               'new_zero_proportion_proven': False, 'seconds': time.monotonic()-started}
    output = HERE/'cover-cross-moment-exact-rows-replay.json'
    output.write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf8')
    print(json.dumps({'all_checks_passed': True, 'cases': results, 'seconds': receipt['seconds'],
                      'interface_sha256': receipt['exact_interface_sha256'], 'receipt_sha256': sha(output.read_bytes())}), flush=True)


if __name__ == '__main__':
    main()
