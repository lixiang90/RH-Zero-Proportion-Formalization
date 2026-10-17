"""Freeze capped-campaign proof/source evidence after all independent replay.

Losslessly gzip closed JSONL receipts, retaining both raw/compressed hashes.
Exclude large databases and the old JSON. No search or source mutation.
"""
from pathlib import Path
import argparse, gzip, hashlib, json

HERE = Path(__file__).parent
ROOT = HERE.parent


def sha_file(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1<<20), b''):
            h.update(chunk)
    return h.hexdigest()


def record(path):
    return {'path': path.relative_to(ROOT).as_posix(), 'bytes': path.stat().st_size, 'sha256': sha_file(path)}


def main():
    ap = argparse.ArgumentParser(description=__doc__);ap.add_argument('--folder', type=Path, required=True)
    ap.add_argument('--manifest', type=Path, required=True);args = ap.parse_args();assert not args.manifest.exists()
    folder = args.folder.resolve();load = lambda n: json.loads((folder/n).read_bytes())
    progress = load('progress.json');stream = load('final-stream-replay.json');standalone = load('standalone-replay.json')
    exported = load('standalone-export.json');epoch = load('epoch.json')
    assert progress['stage'] == 'capped_campaign_and_full_new_journal_replay_finished'
    assert progress['final_stream_replay_passed'] and stream['passed'] and standalone['passed']
    n = progress['committed_campaign_nodes'];assert 0 < n <= 10000
    assert stream['new_campaign_nodes'] == standalone['campaign_nodes'] == n
    assert stream['journal_nodes_replayed'] == standalone['journal_nodes'] == n+1004
    assert progress['state'] == stream['final_state'] == standalone['final_state']
    assert progress['journal_head'] == stream['journal_head'] == standalone['journal_head']
    prefix = load('prefix-stream-replay.json');s = progress['state']
    assert s['checked'] == epoch['prefix_checked']+n
    assert progress['new_Newton_steps'] == s['contraction_steps']-epoch['prefix_state']['contraction_steps']
    assert progress['new_OBBT_bounds'] == s['sublevel_bounds']-epoch['prefix_state']['sublevel_bounds']
    for key, report_key in [('Newton_steps', 'new_Newton_steps'), ('OBBT_bounds', 'new_OBBT_bounds')]:
        assert stream['totals'][key] == standalone['totals'][key]
        assert stream['totals'][key]-prefix['totals'][key] == progress[report_key]
    assert exported['archive_sha256'] == standalone['archive_sha256'] == sha_file(folder/'standalone.jsonl.gz')
    assert exported['uncompressed_stream_sha256'] == standalone['uncompressed_stream_sha256']
    for name, expected in epoch['source_guards'].items():
        assert sha_file(ROOT/Path(name.replace('\\', '/'))) == expected
    max_checker = 0;gates = 0
    with (folder/'node-gates.jsonl').open(encoding='utf8') as f:
        for line in f:
            row = json.loads(line);gates += 1
            max_checker = max(max_checker, row['committed']['checker_RSS_bytes'])
    assert gates == n
    logs = [];compressed = []
    for name in ['node-gates.jsonl', 'metrics.jsonl', 'final-stream-nodes.jsonl', 'standalone-replay-nodes.jsonl']:
        source = folder/name;target = source.with_name(source.name+'.gz');assert not target.exists()
        before = source.stat();h = hashlib.sha256()
        with source.open('rb') as inp, target.open('xb') as out:
            with gzip.GzipFile(fileobj=out, mode='wb', mtime=0) as gz:
                for chunk in iter(lambda: inp.read(1<<20), b''):
                    h.update(chunk);gz.write(chunk)
        assert before.st_size == source.stat().st_size and before.st_mtime_ns == source.stat().st_mtime_ns
        logs.append({'raw_path': source.relative_to(ROOT).as_posix(), 'raw_bytes': before.st_size,
          'raw_sha256': h.hexdigest(), 'gzip': record(target)})
        compressed.append(target)
    packed_receipt = folder/'log-compression.json';assert not packed_receipt.exists()
    packed_receipt.write_text(json.dumps({'scope': 'Lossless receipt compression; no witness pruning.',
      'files': logs, 'new_zero_proportion_proven': False}, indent=2)+'\n', encoding='utf8')
    import cover_sqlite_bounded143004_parts as parts
    pieces_manifest = folder/'standalone-parts.json'
    pieces = parts.split(folder/'standalone.jsonl.gz', pieces_manifest)
    assert pieces['gzip_sha256'] == standalone['archive_sha256']
    note = folder/'SUMMARY.md';assert not note.exists();s = progress['state'];cache = progress['final_cache']
    note.write_text(f'''# Capped SQLite campaign

The authorized campaign committed {n} additional nodes from133004 to{s['checked']}
and stopped for `{progress['stop_reason']}`. The hard endpoint was143004;
the original2022500-node total budget was not expanded. No full-budget
search or historical132000-node semantic replay was performed.

Every candidate passed a resident independent mathematical gate. Each
commit was checked against its predicted complete units, counter/frontier
delta and hash head before another candidate started. A fresh process
then streamed all{n+1004} new journal nodes from the original25-cell boundary,
checking every OBBT/Newton chain, leaf and child cell without a record list.
The separate standalone gzip streams the same complete packets and passed
the same mathematics/hash/counter reconstruction without the large DB.
The initial boundary remains conditional on the historical baseline.

The campaign exercised {progress['new_Newton_steps']} actual Newton steps and
{progress['new_OBBT_bounds']} new OBBT bounds. First actual Newton:
`{progress['first_actual_Newton']}`. These are exact finite replay results,
not additional actual Lean theorem instantiations or a global zero bound.

Final state: {s['accepted_count']} accepted, {s['unresolved_count']} pending;
{s['contraction_steps']} cumulative Newton steps and {s['sublevel_bounds']}
cumulative OBBT bounds. Pending is a DFS count, not a volume/work fraction.
Journal head: `{progress['journal_head']}`.

Producer peak working set: {cache['peak_working_set_bytes']}bytes.
Largest resident-checker RSS at a durable node: {max_checker}bytes.
The1.5GiB guard is tested after a verified durable node, for both processes;
it is not a hard operating-system allocation limit. HINTS was never cleared
and ended with {cache['HINTS_interval_keys']} interval keys/{cache['HINTS_points']}
points. Caches retain their original policies. This finite campaign does
not establish bounded cache growth in a complete search.

The original132000 snapshot,132004 prefix and133004 campaign databases remain separate.
The producer and checker started as fresh processes with cold volatile caches;
no original HINTS trajectory continuation is claimed.
The new database, raw receipt logs and runtime lock are excluded from the
small pin. Receipt logs are preserved losslessly in gzip with both hashes.
The standalone witness archive is {standalone['archive_bytes']}bytes,
SHA `{standalone['archive_sha256']}`. Full discovery, historical proof
replay, complete-cover Lean consumption and a new unconditional record
remain unfinished. No such flags are asserted.

The whole gzip is excluded from the cloud pin in favor of exact byte
pieces of at most4MiB. Each piece and their concatenation were independently
re-read and hash checked after the complete gzip mathematical replay.
The parts replayer reconstructs a verified temporary gzip with bounded
memory before invoking the same independent mathematical stream verifier.
''', encoding='utf8')
    sources = [HERE/n for n in ['window_sqlite_bounded143004.py', 'cover_sqlite_campaign_math.py',
      'cover_sqlite_bounded143004_checker.py', 'cover_sqlite_bounded143004_archive.py',
      'cover_sqlite_bounded143004_finish.py', 'cover_sqlite_bounded143004_parts.py', Path(__file__).name]]
    data = [folder/n for n in ['epoch.json', 'transaction-regression.json', 'prefix-stream-replay.json',
      'final-stream-replay.json', 'progress.json', 'standalone-export.json',
      'standalone-replay.json', 'log-compression.json', 'SUMMARY.md']]+compressed
    data += [pieces_manifest]+[folder/r['name'] for r in pieces['pieces']]
    files = [record(p) for p in sources+data]
    manifest = {'scope': __doc__, 'files': files, 'file_count': len(files),
      'total_bytes': sum(r['bytes'] for r in files), 'source_epoch': epoch,
      'four_node_prefix_manifest': record(HERE/'cover-sqlite-real-node-files.json'),
      'campaign133004_prefix_manifest': record(HERE/'cover-sqlite-campaign133004-files.json'),
      'cold_process_cache': True, 'original_HINTS_trajectory_continuation': False,
      'storage_prototype_manifest': record(HERE/'cover-sqlite-proof-store-files.json'),
      'new_campaign_nodes': n, 'streamed_journal_nodes': n+1004,
      'all_candidate_math_and_commit_delta_gates_passed': True, 'final_stream_math_replay_passed': True,
      'standalone_math_replay_passed': True, 'final_state': s, 'final_journal_head': progress['journal_head'],
      'actual_Newton_steps_exercised': progress['new_Newton_steps'], 'actual_OBBT_bounds_exercised': progress['new_OBBT_bounds'],
      'producer_peak_working_set_bytes': cache['peak_working_set_bytes'], 'resident_checker_max_durable_RSS_bytes': max_checker,
      'excluded_new_database': {'path': (folder/'campaign.sqlite').relative_to(ROOT).as_posix(),
        'bytes': progress['database_bytes'], 'sha256': progress['database_sha256']},
      'excluded_raw_logs': [r['raw_path'] for r in logs],
      'excluded_whole_gzip': record(folder/'standalone.jsonl.gz'),
      'standalone_pieces_exact_combined_hash_checked': True,
      'standalone_replay_command': 'python -B -X utf8 research-goal-20261016/cover_sqlite_bounded143004_parts.py --parts research-goal-20261016/sqlite-bounded143004/standalone-parts.json --receipt NEW_RECEIPT.json --node-log NEW_NODE_LOG.jsonl',
      'historical_baseline_semantic_replay': False, 'complete_global_cover': False,
      'full_budget_search_started': False, 'new_zero_proportion_proven': False}
    args.manifest.write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf8')
    print(json.dumps({'manifest_sha256': sha_file(args.manifest), 'files': len(files), 'bytes': manifest['total_bytes']}), flush=True)


if __name__ == '__main__':
    main()
