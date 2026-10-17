"""Stream a capped campaign's new journal into a standalone gzip proof.

Only the conditional old frontier/metadata and <=11004 new node packets
are exported, never the132000 historical proofs. Replay streams one node
at a time through the frozen independent mathematical checker. No search,
optimizer, full historical semantic replay or global claim is performed.
"""
from pathlib import Path
import argparse, gzip, hashlib, json, sqlite3, time

HERE = Path(__file__).parent
ROOT = HERE.parent


def C(v):
    return json.dumps(v, sort_keys=True, ensure_ascii=True, allow_nan=False, separators=(',', ':')).encode('ascii')


def sha(b):
    return hashlib.sha256(b).hexdigest()


def get(db, table, name):
    row = db.execute(f'SELECT payload FROM {table} WHERE name=?', (name,)).fetchone();assert row
    return json.loads(row[0])


def file_sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1<<20), b''):
            h.update(block)
    return h.hexdigest()


def export(folder, archive):
    progress = json.loads((folder/'progress.json').read_bytes())
    assert progress['stage'] == 'capped_campaign_and_full_new_journal_replay_finished' and progress['final_stream_replay_passed']
    db = sqlite3.connect((folder/'campaign.sqlite').resolve().as_uri()+'?mode=ro', uri=True)
    db.execute('PRAGMA cache_size=-8192');db.execute('BEGIN')
    header = {'kind': 'header', 'schema': 'sqlite-bounded143004-stream-conditional-v1',
      'baseline': get(db, 'control', 'baseline'), 'baseline_commit': get(db, 'control', 'baseline_commit'),
      'baseline_metadata': get(db, 'control', 'baseline_metadata'), 'pilot_epoch': get(db, 'control', 'pilot_epoch'),
      'campaign_epoch': get(db, 'control', 'campaign_epoch'),
      'bounded143004_epoch': get(db, 'control', 'bounded143004_epoch'),
      'initial_frontier': [json.loads(r[0]) for r in db.execute("SELECT payload FROM entries WHERE section='unresolved' ORDER BY position")]}
    nodes = 0;raw_hash = hashlib.sha256()
    with archive.open('xb') as out:
        with gzip.GzipFile(fileobj=out, mode='wb', mtime=0) as packed:
            def emit(value):
                raw = C(value)+b'\n';packed.write(raw);raw_hash.update(raw)
            emit(header)
            for sequence, path, payload, digest, previous, committed in db.execute('SELECT * FROM node_log ORDER BY sequence'):
                assert 1 <= sequence <= 11004 and sha(payload) == digest
                packet = json.loads(payload);units = []
                r = packet['resolution'];supplies = [('sublevel_contractions', packet['OBBT']),
                  ('contractions', packet['Newton'] or None),
                  ('accepted' if r['kind'] == 'leaf' else 'branches', r.get('leaf', r.get('branch')))]
                for section, value in supplies:
                    row = db.execute('SELECT position,payload,digest FROM entries WHERE section=? AND item_key=?', (section, path)).fetchone()
                    if value is None:
                        assert row is None
                    else:
                        assert row and row[1] == C(value) and sha(row[1]) == row[2]
                        units.append([section, row[0], path, row[2]])
                for support in packet['supports']:
                    key = str(support[0]);row = db.execute("SELECT position,payload,digest FROM entries WHERE section='tangent_data' AND item_key=?", (key,)).fetchone()
                    assert row and row[1] == C(support) and sha(row[1]) == row[2]
                    units.append(['tangent_data', row[0], key, row[2]])
                emit({'kind': 'node', 'sequence': sequence, 'path': path, 'packet': packet,
                  'packet_digest': digest, 'previous_commit': previous, 'commit': committed, 'units': units});nodes += 1
            emit({'kind': 'footer', 'nodes': nodes, 'state': get(db, 'runtime', 'state'),
              'frontier': [json.loads(r[0]) for r in db.execute('SELECT payload FROM frontier ORDER BY position')],
              'frontier_digest': get(db, 'runtime', 'frontier_sha256'), 'head': get(db, 'runtime', 'journal_commit'),
              'sequence': get(db, 'runtime', 'journal_sequence'),
              'section_counts': dict(db.execute('SELECT section,count(*) FROM entries GROUP BY section')),
              'source_database_sha256': progress['database_sha256'],
              'final_stream_receipt_sha256': file_sha(folder/'final-stream-replay.json'),
              'historical_baseline_semantic_replay': False, 'new_zero_proportion_proven': False})
    db.close();assert nodes == 1004+progress['committed_campaign_nodes']
    return {'archive_bytes': archive.stat().st_size, 'archive_sha256': file_sha(archive),
      'uncompressed_stream_sha256': raw_hash.hexdigest(), 'nodes': nodes,
      'no_node_record_list_accumulated': True}


def replay(archive, receipt, log):
    import cover_sqlite_node_replay as checker
    started = time.monotonic();stream_hash = hashlib.sha256();first_Newton = None
    kinds = {};totals = {'nodes': 0, 'OBBT_bounds': 0, 'Newton_steps': 0};sequence = 0
    with gzip.open(archive, 'rb') as source, log.open('x', encoding='utf8', newline='\n') as output:
        raw = source.readline();stream_hash.update(raw);header = json.loads(raw)
        assert header['kind'] == 'header' and header['schema'] == 'sqlite-bounded143004-stream-conditional-v1'
        meta = header['baseline_metadata'];pilot = header['pilot_epoch'];campaign = header['campaign_epoch'];production = header['bounded143004_epoch']
        assert campaign['maximum_checked'] == 133004 and campaign['original_checked_endpoint'] == 2022500
        assert campaign['prefix_epoch_sha256'] == sha(C(pilot)) and campaign['prefix_sequence'] == 4
        assert production['maximum_checked'] == 143004 and production['maximum_new_nodes'] == 10000
        assert production['original_checked_endpoint'] == 2022500 and production['prefix_sequence'] == 1004
        assert production['prefix_checked'] == 133004 and production['prefix_epoch_sha256'] == sha(C(campaign))
        for name, expected in {**meta['input_sha256'], **pilot['source_guards'], **campaign['source_guards'], **production['source_guards']}.items():
            assert file_sha(ROOT/Path(name.replace('\\', '/'))) == expected
        w = checker.finite.low;assert meta['target'] == '11/1250' and [list(r) for r in w.root()] == meta['root']
        grid = HERE/'cover_newjet.json';assert file_sha(grid) == meta['derivative_grid_sha256']
        checker.finite.direction.install_grid(grid);table = checker.finite.correlated.make_table(grid)
        registry = checker.finite.gram.make_gram_registry();assert registry['sha256'] == meta['Gram_certificate_sha256']
        previous = header['baseline_commit'];assert sha(C(header['baseline'])) == previous
        frontier = header['initial_frontier'];assert sha(C(frontier)) == header['baseline']['frontier_sha256']
        counts = dict(header['baseline']['section_counts'])
        state = {k: meta[k] for k in ['checked', 'accepted_count', 'counts', 'unresolved_count', 'maxdepth',
          'contraction_paths', 'contraction_steps', 'sublevel_contraction_paths', 'sublevel_bounds']}
        state = json.loads(C(state));footer = None
        for raw in source:
            stream_hash.update(raw);row = json.loads(raw)
            if row['kind'] == 'footer':
                footer = row;assert not source.read(1);break
            assert row['kind'] == 'node';sequence += 1;assert row['sequence'] == sequence <= 11004
            packet = row['packet'];assert sha(C(packet)) == row['packet_digest'] and row['previous_commit'] == previous
            incoming = frontier.pop();assert packet['path'] == row['path'] == incoming['path']
            epoch = pilot if sequence <= 4 else campaign if sequence <= 1004 else production
            result = checker.verify_node(packet, incoming, meta, epoch, w, table, registry)
            r = packet['resolution'];units = []
            for section, value in [('sublevel_contractions', packet['OBBT']), ('contractions', packet['Newton'] or None),
              ('accepted' if r['kind'] == 'leaf' else 'branches', r.get('leaf', r.get('branch')))]:
                if value is not None:
                    units.append([section, counts[section], row['path'], sha(C(value))]);counts[section] += 1
            for support in packet['supports']:
                units.append(['tangent_data', counts['tangent_data'], str(support[0]), sha(C(support))]);counts['tangent_data'] += 1
            assert units == row['units']
            frontier.extend(result['children']);state['checked'] += 1;state['unresolved_count'] = len(frontier)
            state['maxdepth'] = max(state['maxdepth'], incoming['depth'])
            if r['kind'] == 'leaf':
                state['accepted_count'] += 1;state['counts'][r['leaf']['kind']] += 1
            if packet['OBBT'] is not None:
                state['sublevel_contraction_paths'] += 1;state['sublevel_bounds'] += result['OBBT_bounds']
            if packet['Newton']:
                state['contraction_paths'] += 1;state['contraction_steps'] += result['Newton_steps']
            committed = sha(C({'previous': previous, 'sequence': sequence, 'node_sha256': row['packet_digest'],
              'frontier_sha256': sha(C(frontier)), 'state': state}))
            assert committed == row['commit'];previous = committed
            if sequence == 4:
                assert committed == campaign['prefix_journal_head'] and state['checked'] == 132004
            if sequence == 1004:
                assert committed == production['prefix_journal_head'] and state == production['prefix_state']
                assert sha(C(frontier)) == production['prefix_frontier_sha256'] and counts == production['prefix_section_counts']
            kind = result['resolution'];kinds[kind] = kinds.get(kind, 0)+1
            totals['nodes'] += 1;totals['OBBT_bounds'] += result['OBBT_bounds'];totals['Newton_steps'] += result['Newton_steps']
            if result['Newton_steps'] and first_Newton is None:
                first_Newton = {'sequence': sequence, 'path': row['path'], 'steps': result['Newton_steps']}
            output.write(C({'sequence': sequence, 'path': row['path'], 'resolution': kind,
              'OBBT_bounds': result['OBBT_bounds'], 'Newton_steps': result['Newton_steps'], 'commit': previous}).decode()+'\n')
            if sequence % 250 == 0:
                print(json.dumps({'archive_nodes_replayed': sequence}), flush=True)
        assert footer and 1004 <= sequence <= 11004
        assert sequence == footer['nodes'] == footer['sequence']
        assert state == footer['state'] and frontier == footer['frontier'] and counts == footer['section_counts']
        assert previous == footer['head'] and sha(C(frontier)) == footer['frontier_digest'] and state['checked'] <= 143004
    result = {'scope': __doc__, 'script_sha256': file_sha(Path(__file__)), 'passed': True,
      'archive_sha256': file_sha(archive), 'archive_bytes': archive.stat().st_size,
      'uncompressed_stream_sha256': stream_hash.hexdigest(), 'journal_nodes': sequence,
      'campaign_nodes': sequence-1004, 'totals': totals, 'resolution_counts': kinds, 'first_actual_Newton': first_Newton,
      'final_state': state, 'journal_head': previous, 'no_node_record_list_accumulated': True,
      'original_JSON_or_large_database_required': False, 'conditional_on_historical_baseline': True,
      'historical_baseline_semantic_replay': False, 'complete_global_cover': False,
      'new_zero_proportion_proven': False, 'seconds': time.monotonic()-started}
    receipt.write_text(json.dumps(result, indent=2)+'\n', encoding='utf8');return result


def main():
    ap = argparse.ArgumentParser(description=__doc__);ap.add_argument('--export', action='store_true')
    ap.add_argument('--folder', type=Path);ap.add_argument('--archive', type=Path, required=True)
    ap.add_argument('--receipt', type=Path, required=True);ap.add_argument('--node-log', type=Path)
    args = ap.parse_args();assert not args.receipt.exists()
    if args.export:
        assert args.folder and not args.archive.exists();result = export(args.folder, args.archive)
        args.receipt.write_text(json.dumps(result, indent=2)+'\n', encoding='utf8')
    else:
        assert args.node_log and not args.node_log.exists();result = replay(args.archive, args.receipt, args.node_log)
    print(json.dumps({k: v for k, v in result.items() if k != 'final_state'}), flush=True)


if __name__ == '__main__':
    main()
