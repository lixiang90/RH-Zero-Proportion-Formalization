"""Small isolated storage tests; no kernel evaluation or actual cover search.

Exercise baseline roundtrip, genuine process exit before commit, rollback,
source guards, duplicate/stale nodes, support conflicts, atomic counters,
and immutable baseline retention after node commits. Toy witnesses are
opaque placeholders and carry no mathematical claim.
"""
from pathlib import Path
from fractions import Fraction
import argparse, hashlib, json, sqlite3, subprocess, sys
import cover_sqlite_proof_store as store
import cover_sqlite_proof_store_replay as replay


def signature(path):
    db = sqlite3.connect(path);h = hashlib.sha256()
    for table in ['control', 'runtime', 'frontier', 'entries', 'node_log']:
        for row in db.execute(f'SELECT * FROM {table} ORDER BY1'.replace('BY1', 'BY 1')):
            converted = [x.decode('ascii') if isinstance(x, bytes) else x for x in row]
            h.update(store.canonical([table, converted]))
    db.close();return h.hexdigest()


def frontier(path):
    db = store.connect(path);value = store.get(db, 'runtime', 'frontier_sha256');db.close();return value


def rejected(database, packet, root, expected, **kw):
    before = signature(database)
    try:
        store.append_node(database, packet, root, expected_frontier_sha256=expected, **kw)
    except (AssertionError, store.InjectedCrash, sqlite3.IntegrityError):
        pass
    else:
        raise AssertionError('Rejected transition unexpectedly committed.')
    assert signature(database) == before


def run(folder):
    assert not folder.exists();folder.mkdir(parents=True)
    guard = folder/'guard.txt';guard.write_bytes(b'frozen-toy-source')
    spans = [(i, i+1) for i in range(9)]+[(i, j) for i in range(9) for j in range(i+2, 10)]
    state = [[(j-i)*32768 for i, j in spans], [(j-i)*65536 for i, j in spans]]
    counts = {k: 0 for k in ['value', 'stationary', 'reflection', 'Gram', 'stationary_empty', 'sublevel_empty']}
    doc = {'format': 'RelevantBelow-KKT-OBBT-compact-v2', 'input_sha256': {'guard.txt': store.sha(guard.read_bytes())},
      'root': state, 'target': '11/1250', 'checked': 0, 'accepted_count': 0, 'counts': counts,
      'unresolved_count': 1, 'maxdepth': 0, 'contraction_paths': 0, 'contraction_steps': 0,
      'sublevel_contraction_paths': 0, 'sublevel_bounds': 0,
      'accepted': [], 'branches': [], 'contractions': {}, 'sublevel_contractions': {},
      'unresolved': [{'path': 'r', 'depth': 0, 'state': state}], 'tangent_data': []}
    source = folder/'baseline.json';source.write_bytes(store.canonical(doc)+b'\n')
    database = folder/'proof.sqlite'
    imported = store.import_snapshot(source, database, folder, expected_source_sha256=store.sha(source.read_bytes()))
    initial_replay = replay.replay(source, database, folder)
    packet = {'path': 'r', 'depth': 0, 'incoming_cell_sha256': store.sha(store.canonical(state)),
      'supports': [[100, 0, 1, 2, 3, 4]], 'OBBT': {'b': [['opaque-toy-bound']], 'sha256': 'toy'},
      'Newton': [{'a': [], 'c': [], 'sha256': 'toy'}],
      'resolution': {'kind': 'branch', 'branch': {'path': 'r', 'axis': 0, 'cut': 49152},
        'children': [{'path': 'r1', 'depth': 1, 'state': state}, {'path': 'r0', 'depth': 1, 'state': state}]}}
    old_frontier = frontier(database)
    rejected(database, packet, folder, old_frontier, fault_at='after_witnesses')
    rejected(database, packet, folder, old_frontier, fault_at='before_commit')
    packet_file = folder/'node.json';packet_file.write_bytes(store.canonical(packet))
    before = signature(database)
    command = [sys.executable, '-S', '-B', '-X', 'utf8', str(Path(__file__).resolve()),
      '--crash-child', str(database.resolve()), '--root', str(folder.resolve()),
      '--packet', str(packet_file.resolve()), '--expected-frontier', old_frontier]
    child = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    assert child.returncode == 77 and signature(database) == before
    guard.write_bytes(b'changed-toy-source');rejected(database, packet, folder, old_frontier)
    guard.write_bytes(b'frozen-toy-source')
    rejected(database, packet, folder, '0'*64)
    committed = store.append_node(database, packet, folder, expected_frontier_sha256=old_frontier)
    assert committed['state']['checked'] == 1 and committed['state']['unresolved_count'] == 2
    assert committed['state']['sublevel_bounds'] == 1 and committed['state']['contraction_steps'] == 1
    rejected(database, packet, folder, committed['frontier_sha256'])
    leaf = {'path': 'r0', 'depth': 1, 'incoming_cell_sha256': store.sha(store.canonical(state)),
      'supports': [[100, 0, 1, 2, 3, 99]], 'OBBT': None, 'Newton': [],
      'resolution': {'kind': 'leaf', 'leaf': {'path': 'r0', 'depth': 1, 'kind': 'reflection'}}}
    rejected(database, leaf, folder, committed['frontier_sha256'])
    leaf['supports'] = [[100, 0, 1, 2, 3, 4]]
    final = store.append_node(database, leaf, folder, expected_frontier_sha256=committed['frontier_sha256'])
    assert final['sequence'] == 2 and final['state']['checked'] == 2
    assert final['state']['accepted_count'] == 1 and final['state']['unresolved_count'] == 1
    assert final['state']['counts']['reflection'] == 1
    final_replay = replay.replay(source, database, folder)
    assert final_replay['post_baseline_node_transactions_present'] == 2
    return {'scope': __doc__, 'source_sha256': store.sha(Path(__file__).read_bytes()),
      'producer_sha256': store.sha(Path(store.__file__).read_bytes()),
      'independent_replay_source_sha256': store.sha(Path(replay.__file__).read_bytes()),
      'toy_baseline_raw_sha256': imported['baseline']['source_sha256'],
      'toy_baseline_canonical_sha256': initial_replay['canonical_document_sha256'],
      'actual_os_exit_before_commit_returncode': child.returncode,
      'tests_passed': ['independent_baseline_roundtrip', 'rollback_after_witnesses', 'rollback_before_commit',
        'real_process_exit_SQLite_recovery', 'source_guard_rejection', 'stale_frontier_rejection',
        'atomic_witness_support_frontier_counter_commit', 'duplicate_node_rejection',
        'conflicting_support_rejection', 'identical_support_reuse', 'second_node_commit',
        'immutable_baseline_roundtrip_after_two_commits'],
      'all_passed': True, 'toy_witnesses_are_mathematically_sound': False,
      'actual_cover_search_started': False, 'new_zero_proportion_proven': False}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--folder', type=Path);ap.add_argument('--receipt', type=Path)
    ap.add_argument('--crash-child', type=Path);ap.add_argument('--root', type=Path)
    ap.add_argument('--packet', type=Path);ap.add_argument('--expected-frontier')
    args = ap.parse_args()
    if args.crash_child:
        store.append_node(args.crash_child, json.loads(args.packet.read_bytes()), args.root,
          expected_frontier_sha256=args.expected_frontier, hard_crash_at='before_commit')
        raise AssertionError('Crash injection returned.')
    assert args.folder and args.receipt and not args.receipt.exists()
    result = run(args.folder);args.receipt.write_text(json.dumps(result, indent=2)+'\n', encoding='utf8')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
