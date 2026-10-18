"""Prepared independent certificate checker; never searches for a graph cycle.

Cycle mode checks only the supplied simple negative cycle against original B/H.
DAG mode verifies all original H edges against the supplied full vertex order.
No producer import, DFS, q construction, FS/point/kernel/matrix/LP or Lean.
"""
import argparse
import gzip
from hashlib import sha256
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import time
import traceback

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PROD = ROOT / 'research-goal-20261018-window-potential-cycle'
N, VERTICES, H_COUNT = 1187, 2374, 15378
N9, NC, KAPPA = 893616123055294719, 893766123055294719, 335544320000000000
SECONDS, BYTES = 60, 8000000
SOURCE_SCHEMA = 'original-margin-potential-negative-cycle-necessary-gate-v1'


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text(encoding='utf8'))


def under_root(name):
    assert isinstance(name, str)
    path = (ROOT / name).resolve()
    assert path.is_relative_to(ROOT)
    return path


def save(name, obj):
    with (HERE / name).open('x', encoding='utf8', newline='\n') as stream:
        json.dump(obj, stream, ensure_ascii=True, indent=2)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())


def packet_size(directory=HERE):
    return sum(p.stat().st_size for p in directory.iterdir() if p.is_file())


def integer(value):
    assert type(value) is str
    result = int(value)
    assert str(result) == value
    return result


def append_pin(refs, name, expected, size=None):
    path = under_root(name)
    actual = digest(path)
    assert actual == expected, name
    if size is not None:
        assert path.stat().st_size == size, name
    if name in refs:
        assert refs[name] == actual
    refs[name] = actual


def input_identity(args):
    refs = {}
    append_pin(refs, args.gate, args.gate_sha256)
    gate = read(under_root(args.gate))
    assert type(gate['independent_window_potential_certificate_audits_authorized']) is int
    assert gate['independent_window_potential_certificate_audits_authorized'] == 1
    assert gate['expected_H_records'] == H_COUNT
    assert gate['resource_limits'] == {'elapsed_seconds': SECONDS, 'closed_output_bytes': BYTES}
    assert type(gate['new_graph_search_q_FS_point_kernel_matrix_LP_or_Lean_authorized']) is int
    assert gate['new_graph_search_q_FS_point_kernel_matrix_LP_or_Lean_authorized'] == 0
    assert gate['automatic_retry_allowed'] is False
    prepared_path = HERE / 'prepared-files.json'
    assert digest(prepared_path) == gate['prepared_manifest_sha256']
    refs[prepared_path.relative_to(ROOT).as_posix()] = digest(prepared_path)
    prepared = read(prepared_path)
    for field in ['files', 'read_only_dependencies']:
        for row in prepared[field]:
            append_pin(refs, row['path'], row['sha256'], row['bytes'])
    runtime = prepared['runtime']
    assert Path(sys.executable).resolve() == Path(runtime['executable']).resolve()
    assert digest(Path(sys.executable)) == runtime['sha256']
    assert sys.version == runtime['version']
    assert sys.flags.optimize == 0
    for row in runtime['additional_files']:
        assert digest(Path(row['path'])) == row['sha256']
        assert Path(row['path']).stat().st_size == row['bytes']
    manifest_row = gate['producer_manifest']
    assert manifest_row['path'] == 'research-goal-20261018-window-potential-cycle/files.json'
    append_pin(refs, manifest_row['path'], manifest_row['sha256'])
    manifest = read(under_root(manifest_row['path']))
    seen_package = set()
    for field in ['files', 'package_files', 'read_only_dependencies', 'dependency_files']:
        for row in manifest.get(field, []):
            append_pin(refs, row['path'], row['sha256'], row.get('bytes'))
            if under_root(row['path']).parent == PROD:
                seen_package.add(row['path'])
    for key, basename in [('producer_result', 'result.json'), ('producer_terminal', 'terminal.json')]:
        row = gate[key]
        assert row['path'] == f'research-goal-20261018-window-potential-cycle/{basename}'
        append_pin(refs, row['path'], row['sha256'])
        assert row['path'] in seen_package, f'{basename} absent from producer file inventory'
    # Independently bound the entire frozen producer folder, including final manifest.
    assert packet_size(PROD) <= BYTES
    return gate, refs, runtime


def original_inputs():
    margins = []
    threshold = 2 * KAPPA * (NC - N9)
    path = ROOT / 'research-goal-20261018-stageB-classification/exception-cells.jsonl.gz'
    with gzip.open(path, 'rt', encoding='ascii') as stream:
        for line in stream:
            row = json.loads(line)
            assert type(row['exception_id']) is int and row['exception_id'] == len(margins)
            assert row['kind'] == 'exception'
            assert row['coordinate_scale'] == 32768 and row['separation'] == '17/20'
            margin = integer(row['original_margin'])
            assert 0 <= margin < threshold
            margins.append(margin)
    assert len(margins) == N
    raw = (ROOT / 'research-goal-20261018-stageH-ordered-transport/remaining-indices.u32.bin').read_bytes()
    assert len(raw) == 4 * H_COUNT
    indices = [entry[0] for entry in struct.iter_unpack('<I', raw)]
    assert len(indices) == H_COUNT
    assert all(type(q) is int and 0 <= q < 4 * N * N for q in indices)
    assert all(a < b for a, b in zip(indices, indices[1:]))
    # This set is membership data only, not an adjacency structure or search.
    return margins, indices, set(indices), threshold


def reconstruct(index, margins, threshold):
    assert type(index) is int and 0 <= index < 4 * N * N
    first_orientation = (index % 4) // 2
    second_orientation = index % 2
    cell_pair = index // 4
    left = cell_pair // N
    right = cell_pair % N
    value = margins[left] + margins[right] - threshold
    assert value < 0
    return {
        'index': index, 'source': 2 * left + first_orientation,
        'target': 2 * right + second_orientation,
        'left_cell': left, 'right_cell': right, 'chart': index % 4,
        'Mleft': str(margins[left]), 'Mright': str(margins[right]), 'weight': str(value),
    }


def check_result(result, terminal, margins, indices, membership, threshold):
    assert result['schema'] == SOURCE_SCHEMA and result['passed'] is True
    assert result['all_H_records_loaded'] == H_COUNT
    assert result['all_edges_strictly_negative'] is True and result['vertices'] == VERTICES
    assert type(result['cycle_found']) is bool
    assert result['q_constructed'] is False
    assert result['new_global_floor_proven'] is False
    assert result['new_unconditional_zero_proportion_proven'] is False
    assert result['website_submission_ready'] is False
    assert type(result['actual_FS_point_kernel_matrix_LP_or_Lean_runs']) is int
    assert result['actual_FS_point_kernel_matrix_LP_or_Lean_runs'] == 0
    assert result['same_family_retry_allowed'] is False
    assert type(terminal['exit_code']) is int and terminal['exit_code'] == 0
    assert terminal['limit_stop'] is None
    assert type(terminal['child_launches']) is int and terminal['child_launches'] == 1
    assert terminal['automatic_retry_allowed'] is False
    assert 0 <= terminal['seconds'] <= SECONDS
    assert 0 <= terminal['closed_output_bytes'] <= BYTES
    assert type(result['pid']) is int and result['pid'] > 0
    assert type(terminal['child_pid']) is int and result['pid'] == terminal['child_pid']
    assert 0 <= result['seconds'] <= SECONDS
    assert result['input_sha256_start'] == result['input_sha256_end']
    for name, expected in result['input_sha256_start'].items():
        assert digest(under_root(name)) == expected, name
    if result['cycle_found']:
        supplied = result['cycle']
        assert isinstance(supplied, list) and 1 <= len(supplied) <= VERTICES
        checked = []
        for edge in supplied:
            index = edge['index']
            assert type(index) is int and index in membership
            assert all(type(edge[key]) is int for key in ['source', 'target', 'left_cell', 'right_cell', 'chart'])
            expected = reconstruct(index, margins, threshold)
            assert edge == expected
            checked.append(expected)
        assert len({edge['source'] for edge in checked}) == len(checked)
        assert len({edge['index'] for edge in checked}) == len(checked)
        for position, edge in enumerate(checked):
            assert edge['target'] == checked[(position + 1) % len(checked)]['source']
        total = sum(integer(edge['weight']) for edge in checked)
        assert total == integer(result['exact_cycle_weight']) and total < 0
        assert result['fixed_scalar_potential_model_refuted'] is True
        return {
            'mode': 'given_simple_negative_cycle_only', 'checked_cycle': checked,
            'checked_edge_count': len(checked), 'exact_cycle_weight': str(total),
            'all_15378_edges_reconstructed': False,
            'simple_directed_cycle_verified': True,
            'fixed_scalar_outer_potential_model_refuted': True,
            'interpretation': 'The supplied cycle makes (P) impossible. It is not a physical multistep or actual energy counterexample.',
        }
    order = result['topological_order']
    assert isinstance(order, list) and len(order) == VERTICES
    assert all(type(vertex) is int and 0 <= vertex < VERTICES for vertex in order)
    assert len(set(order)) == VERTICES
    rank = {vertex: position for position, vertex in enumerate(order)}
    for index in indices:
        edge = reconstruct(index, margins, threshold)
        assert rank[edge['source']] < rank[edge['target']]
    assert result['fixed_scalar_potential_model_refuted'] is False
    return {
        'mode': 'full_given_topological_order', 'checked_edge_count': H_COUNT,
        'all_15378_edges_reconstructed': True, 'full_topological_order_verified': True,
        'topological_order_sha256': sha256(struct.pack('<' + 'I' * VERTICES, *order)).hexdigest(),
        'fixed_scalar_outer_potential_model_refuted': False,
        'interpretation': 'Only the underpaid subgraph is acyclic. Paid/star constraints, existence of q and cumulative energy remain unproved.',
    }


def run_child(args):
    started = time.monotonic()
    stage, refs = 'gate_and_identity', {}
    assert not any((HERE / name).exists() for name in ['started.json', 'independent-review.json', 'failure.json'])
    try:
        gate, refs, runtime = input_identity(args)
        save('started.json', {'pid': os.getpid(), 'time_unix': time.time(), 'attempts': 1, 'input_sha256': refs})
        stage = 'read_original_B_margins_and_H_membership'
        margins, indices, membership, threshold = original_inputs()
        stage = 'check_supplied_certificate_without_search'
        result = read(under_root(gate['producer_result']['path']))
        terminal = read(under_root(gate['producer_terminal']['path']))
        checks = check_result(result, terminal, margins, indices, membership, threshold)
        after = {name: digest(under_root(name)) for name in refs}
        assert after == refs
        elapsed = time.monotonic() - started
        assert elapsed <= SECONDS and packet_size() < BYTES
        review = {
            'schema': 'independent-window-potential-certificate-audit-v1', 'passed': True,
            'pid': os.getpid(), 'producer_cycle_found': result['cycle_found'],
            'original_B_margins_loaded': N, 'original_H_indices_loaded': H_COUNT,
            'threshold': str(threshold), 'checks': checks,
            'input_sha256_start': refs, 'input_sha256_end': after,
            'runtime': runtime, 'seconds': elapsed,
            'producer_imported': False, 'new_graph_search_performed': False,
            'q_FS_point_kernel_matrix_LP_or_Lean_runs': 0,
            'new_global_floor_proven': False, 'website_submission_ready': False,
            'automatic_retry_allowed': False,
        }
        save('independent-review.json', review)
        assert packet_size() <= BYTES
        print(json.dumps({'passed': True, 'mode': checks['mode'], 'checked_edges': checks['checked_edge_count'], 'seconds': elapsed}), flush=True)
    except BaseException as exc:
        save('failure.json', {'passed': False, 'stage': stage, 'error': repr(exc),
                              'traceback': traceback.format_exc(), 'input_sha256': refs,
                              'seconds': time.monotonic() - started, 'automatic_retry_allowed': False})
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--launch-authorized-once', action='store_true')
    parser.add_argument('--child-authorized-once', action='store_true')
    parser.add_argument('--gate', required=True)
    parser.add_argument('--gate-sha256', required=True)
    args = parser.parse_args()
    if args.child_authorized_once:
        run_child(args)
        return
    assert args.launch_authorized_once and not (HERE / 'launch.json').exists()
    input_identity(args)
    command = [sys.executable, '-B', '-X', 'utf8', str(Path(__file__)), '--child-authorized-once',
               '--gate', args.gate, '--gate-sha256', args.gate_sha256]
    save('launch.json', {'parent_pid': os.getpid(), 'command': command, 'child_launches': 1,
                         'gate_sha256': args.gate_sha256,
                         'resource_limits': {'elapsed_seconds': SECONDS, 'closed_output_bytes': BYTES}})
    start, stop = time.monotonic(), None
    with (HERE / 'stdout.log').open('xb') as out, (HERE / 'stderr.log').open('xb') as err:
        proc = subprocess.Popen(command, cwd=ROOT, stdout=out, stderr=err)
        save('child.json', {'parent_pid': os.getpid(), 'child_pid': proc.pid})
        print(json.dumps({'stage': 'independent_certificate_audit_live', 'pid': proc.pid}), flush=True)
        while proc.poll() is None:
            if time.monotonic() - start > SECONDS or packet_size() > BYTES:
                stop = 'hard_resource_limit_inconclusive'
                proc.terminate()
                break
            time.sleep(.2)
        code = proc.wait()
    elapsed = time.monotonic() - start
    if elapsed > SECONDS or packet_size() > BYTES:
        stop = stop or 'closed_resource_limit_inconclusive'
    save('terminal.json', {'exit_code': code, 'seconds': elapsed, 'child_pid': proc.pid,
                           'limit_stop': stop, 'child_launches': 1,
                           'automatic_retry_allowed': False, 'closed_output_bytes': packet_size()})
    print(json.dumps({'terminal_exit_code': code, 'limit_stop': stop}), flush=True)
    if code or stop:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
