"""Seal this fixed bounded epoch after its own final stream replay succeeds.

This process performs no search, database writes or producer recovery.
It waits for the designated new folder, then uses exclusive new outputs
for export, independent standalone replay and the immutable small pin.
"""
from pathlib import Path
import argparse, json, subprocess, sys, time

HERE = Path(__file__).resolve().parent


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--folder', type=Path, required=True)
    ap.add_argument('--manifest', type=Path, required=True)
    args = ap.parse_args();folder = args.folder.resolve()
    assert folder.name == 'sqlite-bounded143004' and not args.manifest.exists()
    started = time.monotonic();last = -1
    while True:
        assert time.monotonic()-started < 21600, 'six-hour wait cap; no recovery attempted'
        p = json.loads((folder/'progress.json').read_bytes())
        assert p['hard_stop_checked'] == 143004
        assert p['original_checked_endpoint'] == 2022500
        assert not p.get('failure'), p
        n = p['committed_campaign_nodes']
        if n//500 != last:
            print(json.dumps({'waiting_for_verified_epoch_finish': n,
              'stage': p['stage']}), flush=True);last = n//500
        if p['stage'] == 'capped_campaign_and_full_new_journal_replay_finished':
            assert p['final_stream_replay_passed'] and 0 < n <= 10000
            break
        time.sleep(5)
    prefix = [sys.executable, '-B', '-X', 'utf8']
    archive = folder/'standalone.jsonl.gz'
    tasks = [
      [str(HERE/'cover_sqlite_bounded143004_archive.py'), '--export', '--folder', str(folder),
       '--archive', str(archive), '--receipt', str(folder/'standalone-export.json')],
      [str(HERE/'cover_sqlite_bounded143004_archive.py'), '--archive', str(archive),
       '--receipt', str(folder/'standalone-replay.json'), '--node-log', str(folder/'standalone-replay-nodes.jsonl')],
      [str(HERE/'cover_sqlite_bounded143004_freeze.py'), '--folder', str(folder),
       '--manifest', str(args.manifest.resolve())]]
    for task in tasks:
        result = subprocess.run(prefix+task)
        assert result.returncode == 0, ('finalization stopped; no automatic retry', task, result.returncode)
    print(json.dumps({'sealed_manifest': str(args.manifest.resolve()),
      'search_nodes_started_by_this_process': 0, 'seconds': time.monotonic()-started}), flush=True)


if __name__ == '__main__':
    main()
