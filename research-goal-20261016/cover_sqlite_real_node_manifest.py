"""Freeze small real-node integration proof material; exclude local databases."""
from pathlib import Path
import argparse, hashlib, json

HERE = Path(__file__).parent
ROOT = HERE.parent
sha = lambda b: hashlib.sha256(b).hexdigest()


def record(path):
    raw = path.read_bytes()
    return {'path': path.relative_to(ROOT).as_posix(), 'bytes': len(raw), 'sha256': sha(raw)}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True);args = ap.parse_args();assert not args.output.exists()
    folder = HERE/'sqlite-real-node-pilot';progress = json.loads((folder/'progress.json').read_bytes())
    standalone = json.loads((folder/'standalone-replay.json').read_bytes())
    epoch = json.loads((folder/'epoch.json').read_bytes())
    assert progress['stage'] == 'bounded_pilot_finished' and len(progress['records']) == 4
    assert progress['all_committed_nodes_math_and_journal_replayed'] and progress['HINTS_were_never_cleared']
    assert standalone['passed'] and standalone['new_nodes'] == 4 and standalone['Newton_steps_actually_exercised'] == 0
    assert standalone['archive_sha256'] == sha((folder/'standalone.json.gz').read_bytes())
    for name, digest in epoch['source_guards'].items():
        assert sha((ROOT/name).read_bytes()) == digest
    files = [HERE/name for name in ['window_sqlite_node_pilot.py', 'cover_sqlite_node_replay.py',
      'cover_sqlite_pilot_archive.py', 'cover_sqlite_real_node_pilot_note.md', Path(__file__).name]]
    files += [folder/name for name in ['epoch.json', 'progress.json', 'standalone.json.gz', 'standalone-replay.json']]
    for number in range(1, 5):
        for suffix in ['json', 'candidate-replay.json', 'journal-replay.json']:
            files.append(folder/f'node{number:02d}.{suffix}')
    records = [record(p) for p in files]
    last = progress['records'][-1]['commit']
    manifest = {'scope': __doc__, 'files': records, 'file_count': len(records),
      'total_bytes': sum(r['bytes'] for r in records),
      'source_epoch_guards': epoch['source_guards'],
      'dependency_store_manifest': record(HERE/'cover-sqlite-proof-store-files.json'),
      'dependency_stopped_snapshot_manifest': record(HERE/'cover-main-stopped-files.json'),
      'excluded_baseline_database': 'research-goal-20261016/main132000-proof-store.sqlite',
      'excluded_pilot_database': {'path': 'research-goal-20261016/sqlite-real-node-pilot/pilot.sqlite',
        'sha256': progress['database_sha256'], 'bytes': progress['database_bytes']},
      'excluded_runtime_writer_marker': 'research-goal-20261016/sqlite-real-node-pilot/writer.lock',
      'all_four_real_nodes_math_and_chain_replayed': True,
      'actual_Newton_steps_exercised': 0, 'new_support_insertions_exercised': 0,
      'final_state': last['state'], 'final_journal_head': last['commit'],
      'standalone_replay_command': 'python -B -X utf8 research-goal-20261016/cover_sqlite_pilot_archive.py --archive research-goal-20261016/sqlite-real-node-pilot/standalone.json.gz --receipt NEW_RECEIPT.json',
      'HINTS_cleared': False, 'producer_peak_working_set_bytes': progress['cache_history'][-1]['peak_working_set_bytes'],
      'long_run_cache_growth_bounded': False, 'historical_baseline_semantic_replay': False,
      'actual_Lean_new_node_theorems_compiled': False, 'complete_global_cover': False,
      'full_budget_search_started': False, 'new_zero_proportion_proven': False}
    args.output.write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf8')
    print(json.dumps({'sha256': sha(args.output.read_bytes()), 'files': len(records),
                      'bytes': manifest['total_bytes']}), flush=True)


if __name__ == '__main__':
    main()
