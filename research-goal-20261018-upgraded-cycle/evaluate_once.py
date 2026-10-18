"""Prepared fixed nine-edge test, using only independently audited J bounds.

No graph search, q construction, FS, point, kernel, matrix, LP or Lean call.
The original K cycle is not replaced if the stronger weights cease to be negative.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import json
import os
import struct
import sys
import time
import traceback

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
EXPECTED = (2867814, 23816, 90540, 390637, 1543511, 484431, 157722, 1232184, 2912941)
TARGET = 4 * 335544320000000000 * 893766123055294719


def pin(path):
    return sha256(path.read_bytes()).hexdigest()


def local(name):
    path = (ROOT / name).resolve()
    assert path.is_relative_to(ROOT)
    return path


def read(path):
    return json.loads(path.read_text(encoding='utf8'))


def save(name, obj):
    with (HERE / name).open('x', encoding='utf8', newline='\n') as out:
        json.dump(obj, out, indent=2)
        out.write('\n')
        out.flush()
        os.fsync(out.fileno())


def uleb(number):
    data = bytearray()
    while number >= 128:
        data.append((number & 127) | 128)
        number >>= 7
    data.append(number)
    return bytes(data)


def load_records(data, indices):
    assert data[:5] == b'JLB2\n'
    at, selected = 5, {}
    for expected_index in indices:
        assert at + 5 <= len(data)
        index, tag = struct.unpack_from('<I', data, at)[0], data[at + 4]
        at += 5
        assert index == expected_index and 0 <= tag <= 3
        numerator = None
        if tag in (1, 2):
            start, number, shift = at, 0, 0
            while True:
                assert at < len(data) and shift < 4096
                value = data[at]
                at += 1
                number |= (value & 127) << shift
                if value < 128:
                    break
                shift += 7
            assert data[start:at] == uleb(number)
            numerator = number // 2 if number % 2 == 0 else -(number // 2) - 1
        if index in EXPECTED:
            selected[index] = (tag, numerator)
    assert at == len(data) and set(selected) == set(EXPECTED)
    return selected


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--evaluate-authorized-once', action='store_true')
    ap.add_argument('--gate')
    ap.add_argument('--gate-sha256')
    args = ap.parse_args()
    if not args.evaluate_authorized_once:
        print(json.dumps({'prepared_only': True, 'mathematical_executions': 0}))
        return
    assert args.gate and args.gate_sha256
    assert not any((HERE / name).exists() for name in ['started.json', 'result.json', 'failure.json'])
    started, refs = time.monotonic(), {}
    try:
        gate_path = local(args.gate)
        assert pin(gate_path) == args.gate_sha256
        gate = read(gate_path)
        assert gate['fixed_nine_edge_upgraded_cycle_evaluations_authorized'] == 1
        assert gate['new_graph_q_FS_point_kernel_matrix_optimizer_Lean_authorized'] == 0
        assert gate['automatic_retry_allowed'] is False
        assert gate['resource_limits'] == {'elapsed_seconds': 60, 'closed_output_bytes': 8000000}
        assert pin(Path(__file__)) == gate['script_sha256']
        refs = {args.gate: args.gate_sha256, **gate['input_sha256']}
        refs[Path(__file__).relative_to(ROOT).as_posix()] = gate['script_sha256']
        for name, expected in refs.items():
            assert pin(local(name)) == expected
        save('started.json', {'pid': os.getpid(), 'time_unix': time.time(), 'input_sha256': refs,
                              'mathematical_evaluations': 1})
        assert read(local(gate['J_independent_receipt']))['passed'] is True
        assert read(local(gate['K_independent_receipt']))['passed'] is True
        cycle = read(local(gate['K_producer_result']))['cycle']
        assert tuple(edge['index'] for edge in cycle) == EXPECTED
        basis = read(local(gate['J_basis']))
        assert int(basis['target']) == TARGET and len(basis['charts']) == 4
        raw_indices = local(gate['H_indices']).read_bytes()
        assert len(raw_indices) == 4 * 15378
        indices = [entry[0] for entry in struct.iter_unpack('<I', raw_indices)]
        assert indices == sorted(set(indices))
        records = load_records(local(gate['J_classifications']).read_bytes(), indices)
        edges = []
        for edge in cycle:
            index, chart = edge['index'], edge['index'] % 4
            assert edge['chart'] == chart
            tag, numerator = records[index]
            baseline = 24 * int(edge['weight'])
            improved = None
            if tag in (1, 2):
                denominator = basis['charts'][chart]['denominator']
                assert type(denominator) is int and 1 <= denominator <= 4 and 12 % denominator == 0
                improved = (12 // denominator) * (numerator - denominator * TARGET)
                assert (tag == 1) == (numerator >= denominator * TARGET)
            else:
                assert numerator is None
                denominator = None
            weight = baseline if improved is None else max(baseline, improved)
            edges.append({'index': index, 'source': edge['source'], 'target': edge['target'],
                          'J_tag': tag, 'J_N': str(numerator) if numerator is not None else None,
                          'J_d': denominator, 'baseline_weight': str(baseline),
                          'valid_J_weight': str(improved) if improved is not None else None,
                          'stronger_weight': str(weight)})
        assert len({edge['source'] for edge in edges}) == 9
        assert all(edge['target'] == edges[(i + 1) % 9]['source'] for i, edge in enumerate(edges))
        total = sum(int(edge['stronger_weight']) for edge in edges)
        original = sum(int(edge['baseline_weight']) for edge in edges)
        assert total >= original
        after = {name: pin(local(name)) for name in refs}
        assert refs == after
        result = {'schema': 'fixed-J-enhanced-nine-cycle-necessary-result-v1', 'passed': True,
                  'pid': os.getpid(), 'seconds': time.monotonic() - started,
                  'input_sha256_start': refs, 'input_sha256_end': after,
                  'edges': edges, 'exact_original_scaled_weight': str(original),
                  'exact_upgraded_cycle_weight': str(total),
                  'fixed_J_enhanced_outer_potential_model_refuted': total < 0,
                  'q_or_global_actual_floor_proven': False,
                  'physical_multistep_counterexample': False,
                  'new_FS_point_kernel_matrix_graphsearch_optimizer_Lean_runs': 0,
                  'new_unconditional_zero_proportion_proven': False, 'website_submission_ready': False,
                  'interpretation': 'Negative sum only refutes the prescribed J-enhanced outer graph. A nonnegative sum only passes this one cycle necessary test.'}
        assert result['seconds'] <= 60
        assert sum(path.stat().st_size for path in HERE.iterdir() if path.is_file()) < 7800000
        save('result.json', result)
        print(json.dumps({'passed': True, 'exact_upgraded_cycle_weight': str(total),
                          'fixed_J_enhanced_outer_potential_model_refuted': total < 0,
                          'seconds': result['seconds']}))
    except BaseException as exc:
        save('failure.json', {'passed': False, 'error': repr(exc), 'traceback': traceback.format_exc(),
                             'seconds': time.monotonic() - started, 'automatic_retry_allowed': False})
        raise


if __name__ == '__main__':
    main()
