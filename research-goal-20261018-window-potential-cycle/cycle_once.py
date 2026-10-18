"""Prepared only: one canonical negative-cycle necessary test, no q search.

Loads all 15378 original H indices before DFS. A directed cycle of these
strictly negative edges refutes only the fixed scalar-margin potential model.
An acyclic result is only a necessary gate, not a cumulative energy proof.
No original FS, test point, kernel, matrix, optimizer or Lean is evaluated.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import gzip
import json
import os
import struct
import subprocess
import sys
import time
import traceback

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
N = 1187
N9 = 893616123055294719
NC = 893766123055294719
KAPPA = 335544320000000000
LIMIT_SECONDS = 60
LIMIT_BYTES = 8000000
PINS = {
    'research-goal-20261018-stageB-classification/files.json': '3f9408f2cf1ceae12339456da034d9e8f175f828cf2d53a652339ee79eec89ad',
    'research-goal-20261018-stageB-classification/exception-cells.jsonl.gz': '180c27713c0473345fd0bb3c3373168a2d79f2e4bf518d5860e1c72cfa8a1ad0',
    'research-goal-20261018-stageB-independent/audit-files.json': 'e6458883bc7588a2302afe435c3b79a08c9236bb895ec3010655024c767d7288',
    'research-goal-20261018-stageH-ordered-transport/files.json': '327562525e30d7b706777e71af003e51ca93a218ac7cfd9bfa0994abe56f8f8c',
    'research-goal-20261018-stageH-ordered-transport/remaining-indices.u32.bin': 'c740852a5757983f462f3a78eb05d1aca5410ffb4077682e3afa48d6f7943559',
    'research-goal-20261018-stageH-independent/audit-files.json': 'a0018aa4ce33e4cb6cea2019739e857fa3a1b58cc8b48f001e17d651e1dcbb3a',
}


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def path_under_root(name):
    path = (ROOT / name).resolve()
    assert path.is_relative_to(ROOT)
    return path


def read(path):
    return json.loads(path.read_text(encoding='utf8'))


def write_new(name, obj):
    with (HERE / name).open('x', encoding='utf8', newline='\n') as out:
        json.dump(obj, out, indent=2)
        out.write('\n')
        out.flush()
        os.fsync(out.fileno())


def size():
    return sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())


def check_gate(args):
    path = path_under_root(args.gate)
    assert digest(path) == args.gate_sha256
    gate = read(path)
    assert gate['canonical_H_negative_cycle_tests_authorized'] == 1
    assert gate['expected_H_records'] == 15378
    assert gate['resource_limits'] == {'elapsed_seconds': 60, 'closed_output_bytes': 8000000}
    assert gate['q_search_optimizer_FS_point_kernel_or_Lean_authorized'] == 0
    assert gate['automatic_retry_allowed'] is False
    refs = {args.gate: args.gate_sha256, **PINS}
    prepared_path = HERE / 'prepared-files.json'
    assert digest(prepared_path) == gate['prepared_manifest_sha256']
    refs[prepared_path.relative_to(ROOT).as_posix()] = gate['prepared_manifest_sha256']
    prepared = read(prepared_path)
    for key in ['files', 'read_only_dependencies']:
        for row in prepared.get(key, []):
            if row['path'] in refs:
                assert refs[row['path']] == row['sha256']
            refs[row['path']] = row['sha256']
    prior = gate['prior_I_independent_receipt']
    refs[prior['path']] = prior['sha256']
    for name, expected in refs.items():
        assert digest(path_under_root(name)) == expected, name
    assert read(path_under_root(prior['path']))['passed'] is True
    return gate, refs


def run_child(args):
    start = time.monotonic()
    stage = 'input_pins'
    refs = {}
    assert not any((HERE / p).exists() for p in ['started.json', 'result.json', 'failure.json'])
    try:
        _gate, refs = check_gate(args)
        write_new('started.json', {'pid': os.getpid(), 'time_unix': time.time(),
                                  'stage': stage, 'input_sha256': refs, 'attempts': 1})
        stage = 'load_all_original_margins_and_H_indices'
        margins = []
        with gzip.open(ROOT / 'research-goal-20261018-stageB-classification/exception-cells.jsonl.gz', 'rt', encoding='ascii') as inp:
            for line in inp:
                rec = json.loads(line)
                assert rec['exception_id'] == len(margins)
                margins.append(int(rec['original_margin']))
        assert len(margins) == N
        threshold = 2 * KAPPA * (NC - N9)
        assert all(0 <= value < threshold for value in margins)
        raw = (ROOT / 'research-goal-20261018-stageH-ordered-transport/remaining-indices.u32.bin').read_bytes()
        assert len(raw) == 4 * 15378
        indices = [row[0] for row in struct.iter_unpack('<I', raw)]
        assert len(indices) == len(set(indices)) == 15378 and indices == sorted(indices)
        adjacency = [[] for _ in range(2 * N)]
        edges = {}
        for index in indices:
            assert 0 <= index < N * N * 4
            pair, chart = divmod(index, 4)
            left, right = divmod(pair, N)
            source, target = 2 * left + chart // 2, 2 * right + chart % 2
            weight = margins[left] + margins[right] - threshold
            assert weight < 0
            edges[index] = {'index': index, 'source': source, 'target': target,
                            'left_cell': left, 'right_cell': right, 'chart': chart,
                            'Mleft': str(margins[left]), 'Mright': str(margins[right]),
                            'weight': str(weight)}
            adjacency[source].append(index)
        stage = 'canonical_iterative_DFS'
        color = [0] * (2 * N)
        parent = [None] * (2 * N)
        postorder = []
        cycle = None
        visited_edges = 0
        ticks = 0
        for root in range(2 * N):
            if color[root]:
                continue
            color[root] = 1
            stack = [(root, 0)]
            while stack and cycle is None:
                ticks += 1
                if ticks % 256 == 0 and (time.monotonic() - start > LIMIT_SECONDS or size() > LIMIT_BYTES):
                    raise RuntimeError('resource_limit_inconclusive')
                node, offset = stack[-1]
                if offset == len(adjacency[node]):
                    color[node] = 2
                    postorder.append(node)
                    stack.pop()
                    continue
                index = adjacency[node][offset]
                stack[-1] = (node, offset + 1)
                visited_edges += 1
                target = edges[index]['target']
                if color[target] == 0:
                    parent[target] = (node, index)
                    color[target] = 1
                    stack.append((target, 0))
                elif color[target] == 1:
                    path = []
                    current = node
                    while current != target:
                        previous, previous_edge = parent[current]
                        path.append(previous_edge)
                        current = previous
                    cycle = list(reversed(path)) + [index]
            if cycle is not None:
                break
        result = {'schema': 'original-margin-potential-negative-cycle-necessary-gate-v1',
                  'passed': True, 'pid': os.getpid(), 'all_H_records_loaded': 15378,
                  'all_edges_strictly_negative': True, 'vertices': 2 * N,
                  'DFS_examined_edges': visited_edges, 'cycle_found': cycle is not None,
                  'input_sha256_start': refs, 'q_constructed': False,
                  'new_global_floor_proven': False, 'new_unconditional_zero_proportion_proven': False,
                  'website_submission_ready': False, 'actual_FS_point_kernel_matrix_LP_or_Lean_runs': 0,
                  'same_family_retry_allowed': False}
        if cycle is not None:
            cert = [edges[index] for index in cycle]
            assert cert and len(cert) <= 2 * N
            assert len({edge['source'] for edge in cert}) == len(cert)
            assert all(edge['target'] == cert[(i + 1) % len(cert)]['source'] for i, edge in enumerate(cert))
            total = sum(int(edge['weight']) for edge in cert)
            assert total < 0
            result.update(cycle=cert, exact_cycle_weight=str(total), fixed_scalar_potential_model_refuted=True,
                          interpretation='Only this scalar outer-graph potential model fails. No physical multistep configuration or actual F counterexample is claimed.')
        else:
            order = list(reversed(postorder))
            rank = {node: i for i, node in enumerate(order)}
            assert len(rank) == 2 * N
            assert all(rank[edge['source']] < rank[edge['target']] for edge in edges.values())
            result.update(topological_order=order, fixed_scalar_potential_model_refuted=False,
                          interpretation='Underpaid subgraph is acyclic. Mixed paid-edge cycles, star constraints and existence of q remain unproved.')
        after = {name: digest(path_under_root(name)) for name in refs}
        assert refs == after
        result['input_sha256_end'] = after
        result['seconds'] = time.monotonic() - start
        write_new('result.json', result)
        print(json.dumps({key: result[key] for key in ['passed', 'cycle_found', 'DFS_examined_edges', 'seconds']}), flush=True)
    except BaseException as exc:
        write_new('failure.json', {'passed': False, 'stage': stage, 'error': repr(exc),
                                  'traceback': traceback.format_exc(), 'input_sha256': refs,
                                  'seconds': time.monotonic() - start, 'automatic_retry_allowed': False})
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--launch-authorized-once', action='store_true')
    parser.add_argument('--child-authorized-once', action='store_true')
    parser.add_argument('--gate')
    parser.add_argument('--gate-sha256')
    args = parser.parse_args()
    assert args.gate and args.gate_sha256
    if args.child_authorized_once:
        run_child(args)
        return
    assert args.launch_authorized_once and not (HERE / 'launch.json').exists()
    gate, _refs = check_gate(args)
    command = [sys.executable, '-B', '-X', 'utf8', str(Path(__file__)), '--child-authorized-once',
               '--gate', args.gate, '--gate-sha256', args.gate_sha256]
    write_new('launch.json', {'parent_pid': os.getpid(), 'command': command, 'child_launches': 1,
                              'gate_sha256': args.gate_sha256, 'resource_limits': gate['resource_limits']})
    start = time.monotonic()
    reason = None
    with (HERE / 'stdout.log').open('xb') as out, (HERE / 'stderr.log').open('xb') as err:
        proc = subprocess.Popen(command, cwd=ROOT, stdout=out, stderr=err)
        write_new('child.json', {'child_pid': proc.pid, 'parent_pid': os.getpid()})
        print(json.dumps({'stage': 'canonical_graph_child_live', 'pid': proc.pid}), flush=True)
        while proc.poll() is None:
            if time.monotonic() - start > LIMIT_SECONDS or size() > LIMIT_BYTES:
                reason = 'hard_resource_limit_inconclusive'
                proc.terminate()
                break
            time.sleep(.2)
        code = proc.wait()
    write_new('terminal.json', {'exit_code': code, 'seconds': time.monotonic() - start,
                                'child_pid': proc.pid, 'limit_stop': reason, 'child_launches': 1,
                                'automatic_retry_allowed': False, 'closed_output_bytes': size()})
    print(json.dumps({'terminal_exit_code': code, 'limit_stop': reason}), flush=True)
    if code or reason:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
