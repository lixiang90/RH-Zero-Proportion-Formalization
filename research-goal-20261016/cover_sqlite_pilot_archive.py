"""Small standalone archive/replay of the four real-node integration pilot.

The complete old baseline is excluded. Its source hash and canonical
baseline descriptor bind a conditional25-cell boundary. Replays all new
node mathematics, supports, child geometry, journal hashes and counters.
Does not replay historical baseline witnesses or resume any search.
"""
from pathlib import Path
import argparse, gzip, hashlib, json, sqlite3, time

HERE = Path(__file__).parent
sha = lambda b: hashlib.sha256(b).hexdigest()


def C(v):
    return json.dumps(v, sort_keys=True, ensure_ascii=True, allow_nan=False, separators=(',', ':')).encode('ascii')


def get(db, table, name):
    row = db.execute(f'SELECT payload FROM {table} WHERE name=?', (name,)).fetchone();assert row
    return json.loads(row[0])


def export(database, output):
    db = sqlite3.connect(database.resolve().as_uri()+'?mode=ro', uri=True);nodes = []
    for seq, path, payload, digest, previous, committed in db.execute('SELECT * FROM node_log ORDER BY sequence'):
        assert 1 <= seq <= 4 and sha(payload) == digest;packet = json.loads(payload);units = []
        supplied = [('sublevel_contractions', packet['OBBT']), ('contractions', packet['Newton'] or None)]
        r = packet['resolution'];supplied.append(('accepted' if r['kind'] == 'leaf' else 'branches', r.get('leaf', r.get('branch'))))
        for section, value in supplied:
            saved = db.execute('SELECT payload,digest FROM entries WHERE section=? AND item_key=?', (section, path)).fetchone()
            if value is None:
                assert saved is None
            else:
                assert saved and C(value) == saved[0] and sha(saved[0]) == saved[1]
                units.append([section, path, saved[1]])
        for support in packet['supports']:
            saved = db.execute("SELECT payload,digest FROM entries WHERE section='tangent_data' AND item_key=?", (str(support[0]),)).fetchone()
            assert saved and saved[0] == C(support) and sha(saved[0]) == saved[1]
            units.append(['tangent_data', str(support[0]), saved[1]])
        nodes.append({'sequence': seq, 'path': path, 'packet': packet, 'packet_digest': digest,
          'previous_commit': previous, 'commit': committed, 'stored_units': units})
    assert len(nodes) == 4
    initial = [json.loads(r[0]) for r in db.execute("SELECT payload FROM entries WHERE section='unresolved' ORDER BY position")]
    final = [json.loads(r[0]) for r in db.execute('SELECT payload FROM frontier ORDER BY position')]
    doc = {'schema': 'sqlite-four-real-node-standalone-v1', 'baseline': get(db, 'control', 'baseline'),
      'baseline_metadata': get(db, 'control', 'baseline_metadata'), 'baseline_commit': get(db, 'control', 'baseline_commit'),
      'epoch': get(db, 'control', 'pilot_epoch'), 'initial_frontier': initial, 'nodes': nodes,
      'final_frontier': final, 'final_state': get(db, 'runtime', 'state'),
      'final_journal_head': get(db, 'runtime', 'journal_commit'),
      'final_journal_sequence': get(db, 'runtime', 'journal_sequence'),
      'final_frontier_digest': get(db, 'runtime', 'frontier_sha256'),
      'final_section_counts': dict(db.execute('SELECT section,count(*) FROM entries GROUP BY section')),
      'historical_baseline_semantic_replay': False, 'new_zero_proportion_proven': False}
    db.close();packed = gzip.compress(C(doc)+b'\n', mtime=0);output.write_bytes(packed)
    return {'gzip_bytes': len(packed), 'gzip_sha256': sha(packed), 'nodes': len(nodes)}


def replay(archive):
    import cover_sqlite_node_replay as math
    started = time.monotonic();raw = archive.read_bytes();doc = json.loads(gzip.decompress(raw))
    assert doc['schema'] == 'sqlite-four-real-node-standalone-v1'
    assert sha(C(doc['baseline'])) == doc['baseline_commit']
    assert sha(C(doc['initial_frontier'])) == doc['baseline']['frontier_sha256']
    db = sqlite3.connect(':memory:');db.execute('CREATE TABLE control(name TEXT PRIMARY KEY,payload BLOB)')
    for key, value in [('baseline_metadata', doc['baseline_metadata']), ('pilot_epoch', doc['epoch'])]:
        db.execute('INSERT INTO control VALUES(?,?)', (key, C(value)))
    meta, epoch, w, table, registry = math.setup(db);db.close()
    frontier = doc['initial_frontier'];state = {k: meta[k] for k in ['checked', 'accepted_count', 'counts',
      'unresolved_count', 'maxdepth', 'contraction_paths', 'contraction_steps', 'sublevel_contraction_paths', 'sublevel_bounds']}
    state = json.loads(C(state));previous = doc['baseline_commit'];results = []
    for seq, node in enumerate(doc['nodes'], 1):
        assert seq == node['sequence'] <= 4 and node['previous_commit'] == previous
        packet = node['packet'];assert sha(C(packet)) == node['packet_digest']
        incoming = frontier.pop();assert incoming['path'] == packet['path'] == node['path']
        result = math.verify_node(packet, incoming, meta, epoch, w, table, registry)
        units = []
        for section, value in [('sublevel_contractions', packet['OBBT']), ('contractions', packet['Newton'] or None)]:
            if value is not None:
                units.append([section, packet['path'], sha(C(value))])
        r = packet['resolution'];section = 'accepted' if r['kind'] == 'leaf' else 'branches'
        units.append([section, packet['path'], sha(C(r.get('leaf', r.get('branch'))))])
        units.extend(['tangent_data', str(s[0]), sha(C(s))] for s in packet['supports'])
        assert units == node['stored_units']
        frontier.extend(result['children']);state['checked'] += 1;state['maxdepth'] = max(state['maxdepth'], incoming['depth'])
        state['unresolved_count'] = len(frontier)
        if r['kind'] == 'leaf':
            state['accepted_count'] += 1;state['counts'][r['leaf']['kind']] += 1
        if packet['OBBT'] is not None:
            state['sublevel_contraction_paths'] += 1;state['sublevel_bounds'] += result['OBBT_bounds']
        if packet['Newton']:
            state['contraction_paths'] += 1;state['contraction_steps'] += result['Newton_steps']
        committed = sha(C({'previous': previous, 'sequence': seq, 'node_sha256': node['packet_digest'],
          'frontier_sha256': sha(C(frontier)), 'state': state}))
        assert committed == node['commit'];previous = committed
        results.append({'path': incoming['path'], **result})
    assert len(results) == doc['final_journal_sequence'] == 4
    assert state == doc['final_state'] and frontier == doc['final_frontier']
    assert previous == doc['final_journal_head'] and sha(C(frontier)) == doc['final_frontier_digest']
    for section, count in [('accepted', state['accepted_count']), ('branches', state['checked']-state['accepted_count']),
      ('contractions', state['contraction_paths']), ('sublevel_contractions', state['sublevel_contraction_paths'])]:
        assert doc['final_section_counts'][section] == count
    return {'scope': __doc__, 'script_sha256': sha(Path(__file__).read_bytes()), 'archive_sha256': sha(raw),
      'archive_bytes': len(raw), 'passed': True, 'independent_node_verifier_sha256': sha(Path(math.__file__).read_bytes()),
      'new_nodes': 4, 'records': results, 'final_state': state, 'final_journal_head': previous,
      'all_new_OBBT_Newton_resolution_and_child_geometry_verified': True,
      'Newton_steps_actually_exercised': sum(r['Newton_steps'] for r in results),
      'entire_new_journal_and_frontier_counters_verified': True,
      'large_database_or_original_JSON_required': False,
      'initial_frontier_is_conditional_on_unreplayed_historical_baseline': True,
      'historical_baseline_semantic_replay': False, 'actual_Lean_new_node_theorems_compiled': False,
      'complete_global_cover': False, 'new_zero_proportion_proven': False,
      'seconds': time.monotonic()-started}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--export', action='store_true');ap.add_argument('--database', type=Path)
    ap.add_argument('--archive', type=Path, required=True);ap.add_argument('--receipt', type=Path)
    args = ap.parse_args()
    if args.export:
        assert args.database and not args.archive.exists();result = export(args.database, args.archive)
    else:
        assert args.receipt and not args.receipt.exists();result = replay(args.archive)
        args.receipt.write_text(json.dumps(result, indent=2)+'\n', encoding='utf8')
    print(json.dumps({k: v for k, v in result.items() if k not in ['records', 'final_state']}), flush=True)


if __name__ == '__main__':
    main()
