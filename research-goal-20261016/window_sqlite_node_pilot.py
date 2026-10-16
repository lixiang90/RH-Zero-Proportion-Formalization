"""At most4 real nodes on a fresh SQLite backup; no full search/resume.

The frozen compact producer's mathematical call order is copied. Historical
witnesses are not loaded: only metadata/runtime/frontier and2540 supports.
Every candidate must pass the independent node mathematics before commit;
after commit the complete short journal is independently replayed before
another node may start. All authoritative mutations use append_node.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, os, sqlite3, subprocess, sys, time
import cover_sqlite_proof_store as store
import window_global_cover as high
import window_lower_global_cover as low
import window_direction_probe as direction
import cover_correlated_api as correlated
import cover_contractor_api as newton
import cover_gram_basin_api as gram
import cover_sublevel_obbt_api as obbt
import cover_compact_codec as codec

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sha = lambda b: hashlib.sha256(b).hexdigest()


def digest_file(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for chunk in iter(lambda: f.read(1<<20), b''):
            h.update(chunk)
    return h.hexdigest()


def check(guards):
    store.check_guards(ROOT, guards)


def cache_state(w, oracle):
    info = {'HINTS_interval_keys': len(w.HINTS), 'HINTS_points': sum(map(len, w.HINTS.values())),
      'USED_SUPPORTS': len(w.USED_SUPPORTS), 'peak_working_set_bytes': store.peak_working_set_bytes()}
    for name, fn in [('constant_lower', w.constant_lower), ('base_anchors', w.base_anchors),
                     ('kernel_jet', w.ik.kernel_jet), ('point', oracle.point), ('affine', oracle.affine),
                     ('third_bound', oracle.third_bound)]:
        info[name] = fn.cache_info()._asdict()
    return info


def run_verifier(database, receipt, candidate=None):
    command = [sys.executable, '-B', '-X', 'utf8', str(HERE/'cover_sqlite_node_replay.py'),
               '--database', str(database), '--receipt', str(receipt)]
    if candidate is not None:
        command += ['--candidate', str(candidate)]
    child = subprocess.run(command, capture_output=True, text=True, encoding='utf8')
    if child.returncode:
        raise RuntimeError(json.dumps({'independent_node_verifier_failed': True, 'exit_code': child.returncode,
          'stdout': child.stdout[-12000:], 'stderr': child.stderr[-12000:]}))
    result = json.loads(receipt.read_bytes());assert result['passed']
    return {'receipt': receipt.name, 'sha256': sha(receipt.read_bytes()), 'seconds': result['seconds']}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-folder', type=Path, required=True)
    ap.add_argument('--baseline', type=Path, default=HERE/'main132000-proof-store.sqlite')
    args = ap.parse_args();folder = args.output_folder.resolve();assert not folder.exists()
    folder.mkdir();lock_path = folder/'writer.lock';lock = lock_path.open('xb')
    lock.write(store.canonical({'pid': os.getpid(), 'created_UTC': datetime.now(timezone.utc).isoformat()}));lock.flush()
    if os.name == 'nt':
        import msvcrt
        lock.seek(0);msvcrt.locking(lock.fileno(), msvcrt.LK_NBLCK, 1)
    else:
        import fcntl
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX|fcntl.LOCK_NB)
    started = time.monotonic();database = folder/'pilot.sqlite';evidence = [];cache_history = []
    report = {'scope': __doc__, 'pilot_PID': os.getpid(), 'nodes_limit': 4, 'records': evidence,
      'cache_history': cache_history, 'baseline_semantic_replay': False, 'full_search_started': False,
      'new_zero_proportion_proven': False}
    def save(stage):
        report['stage'] = stage;report['seconds'] = time.monotonic()-started
        (folder/'progress.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf8')
    try:
        binding = json.loads((HERE/'cover-sqlite-store132000-local-binding.json').read_bytes())
        assert digest_file(args.baseline) == binding['database_sha256']
        source = sqlite3.connect(args.baseline.resolve().as_uri()+'?mode=ro', uri=True)
        destination = store.connect(database)
        source.backup(destination, pages=512);source.close()
        assert destination.execute('PRAGMA integrity_check').fetchone()[0] == 'ok'
        meta = store.get(destination, 'control', 'baseline_metadata')
        assert meta['checked'] == 132000 and meta['target'] == '11/1250'
        assert store.get(destination, 'runtime', 'journal_sequence') == 0
        baseline = store.get(destination, 'control', 'baseline')
        assert baseline['source_sha256'] == binding['baseline_source_sha256']
        assert store.get(destination, 'control', 'baseline_commit') == binding['baseline_commit_recomputed']
        new_sources = [Path(__file__), HERE/'cover_sqlite_proof_store.py', HERE/'cover_sqlite_node_replay.py',
          HERE/'window_compact_obbt_replay.py', HERE/'cover_sublevel_obbt_verify_api.py',
          HERE/'cover_sublevel_obbt_verify.py', HERE/'cover_sublevel_verify.py',
          HERE/'cover_contractor_verify.py', HERE/'cover_correlated_verify.py', HERE/'cover_correlated_replay.py',
          HERE/'cover_compact_checkpoint.py', HERE/'cover_flow_basis.py',
          ROOT/'research-20261016-w10-cert/independent_integer_audit.py']
        guards = {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in new_sources}
        epoch = {'schema': 'sqlite-real-node-pilot-epoch-v1', 'maximum_nodes': 4,
          'baseline_checked': 132000, 'baseline_source_sha256': baseline['source_sha256'],
          'baseline_commit': binding['baseline_commit_recomputed'], 'target': '11/1250',
          'source_guards': guards, 'old_mathematical_sources_unchanged': meta['input_sha256'],
          'single_writer_lock': str(lock_path.relative_to(ROOT)), 'pilot_not_full_budget_resume': True}
        check({**meta['input_sha256'], **guards})
        destination.execute('BEGIN IMMEDIATE');store.put(destination, 'control', 'pilot_epoch', epoch)
        destination.execute('COMMIT');destination.close()
        (folder/'epoch.json').write_bytes(store.canonical(epoch)+b'\n')
        report['epoch_sha256'] = sha(store.canonical(epoch));report['baseline_database_sha256'] = binding['database_sha256']
        report['baseline_source_sha256'] = baseline['source_sha256']
        w = low;g = w.g;grid = HERE/'cover_newjet.json';oracle_sha = direction.install_grid(grid)
        oracle = correlated.make_correlated_oracle(grid);registry = gram.make_gram_registry();engine = obbt.make_engine(w)
        assert oracle_sha == meta['derivative_grid_sha256']
        assert direction.g.TERMS == newton.core.g.TERMS == g.TERMS
        assert direction.g.BS == newton.core.g.BS == g.BS
        known = {};db = store.connect(database, readonly=True)
        for key, payload in db.execute("SELECT item_key,payload FROM entries WHERE section='tangent_data' ORDER BY position"):
            row = json.loads(payload);p, *values = row;assert key == str(p) and p not in known
            known[p] = values;w.USED_SUPPORTS.add(p)
        db.close();assert len(known) == 2540
        report['historical_supports_loaded'] = len(known);cache_history.append({'at': 'initial', **cache_state(w, oracle)})
        save('initialized_before_any_new_node')
        def cheap(state):
            basin = gram.gram_basin(state, '11/1250', registry)
            if basin:
                return 'Gram', basin
            ex = direction.exclusion(state, True)
            if ex is None:
                ex = correlated.correlated_exclusion(state, oracle)
            if ex:
                ex['derivative_grid_sha256'] = oracle_sha;return 'stationary', ex
            return None, None
        for number in range(1, 5):
            check({**meta['input_sha256'], **guards})
            db = store.connect(database, readonly=True)
            top = db.execute('SELECT payload FROM frontier ORDER BY position DESC LIMIT 1').fetchone()
            expected_frontier = store.get(db, 'runtime', 'frontier_sha256');db.close()
            if top is None:
                break
            incoming = json.loads(top[0]);state = (incoming['state'][0], incoming['state'][1])
            path = incoming['path'];depth = incoming['depth'];node_started = time.monotonic()
            packed_obbt = None;packed_newton = [];rec = None
            if state[1][8] < state[0][0]:
                resolution = {'kind': 'leaf', 'leaf': {'path': path, 'depth': depth, 'kind': 'reflection'}}
            else:
                kind, result = cheap(state)
                if kind is None:
                    rec = w.certify(state)
                    if int(rec.get('floor_numerator', '-1')) >= g.TARGET:
                        kind, result = 'value', rec
                if kind is None:
                    assert rec is not None;axis, _ = g.cut(state, rec);axes = sorted(set(list(range(9))+[axis]))
                    refined, bounds = obbt.contract(state, g.TARGET, axes, engine)
                    if bounds:
                        packed_obbt = codec.pack_obbt({'old_cell': state, 'new_cell': refined, 'certificates': bounds})
                        state = refined
                        if state is None:
                            kind, result = 'sublevel_empty', {'reason': 'No F<target point survives epigraph OBBT'}
                        else:
                            kind, result = cheap(state)
                            if kind is None:
                                rec = w.certify(state)
                                if int(rec.get('floor_numerator', '-1')) >= g.TARGET:
                                    kind, result = 'value', rec
                if kind is None:
                    refined, steps, ex = newton.contract(state, 8, oracle)
                    if steps:
                        packed_newton = [codec.pack_newton(step) for step in steps];state = refined
                        if state is None:
                            kind, result = 'stationary_empty', {'reason': 'KKT-only contraction closure is empty'}
                        else:
                            basin = gram.gram_basin(state, '11/1250', registry)
                            if basin:
                                kind, result = 'Gram', basin
                            elif ex:
                                ex['derivative_grid_sha256'] = oracle_sha;kind, result = 'stationary', ex
                            else:
                                kind, result = cheap(state)
                                if kind is None:
                                    rec = w.certify(state)
                                    if int(rec.get('floor_numerator', '-1')) >= g.TARGET:
                                        kind, result = 'value', rec
                if kind is not None:
                    resolution = {'kind': 'leaf', 'leaf': codec.pack_leaf({'path': path, 'depth': depth, 'kind': kind, 'result': result})}
                else:
                    assert state is not None and rec is not None
                    ax, cut = g.cut(state, rec);assert state[0][ax] < cut < state[1][ax];children = []
                    for suffix, upper in [('1', False), ('0', True)]:
                        child = g.split(state, ax, cut, upper)
                        if child is not None:
                            children.append({'path': path+suffix, 'depth': depth+1, 'state': child})
                    resolution = {'kind': 'branch', 'branch': {'path': path, 'axis': ax, 'cut': cut}, 'children': children}
            new_supports = [[p, *w.original_support(p)] for p in sorted(w.USED_SUPPORTS) if p not in known]
            packet = {'path': path, 'depth': depth, 'epoch_sha256': report['epoch_sha256'],
              'incoming_cell_sha256': sha(store.canonical(incoming['state'])), 'supports': new_supports,
              'OBBT': packed_obbt, 'Newton': packed_newton, 'resolution': resolution}
            candidate = folder/f'node{number:02d}.json';candidate.write_bytes(store.canonical(packet)+b'\n')
            before = run_verifier(database, folder/f'node{number:02d}.candidate-replay.json', candidate)
            check({**meta['input_sha256'], **guards})
            committed = store.append_node(database, packet, ROOT, expected_frontier_sha256=expected_frontier)
            check({**meta['input_sha256'], **guards})
            after = run_verifier(database, folder/f'node{number:02d}.journal-replay.json')
            for p, *values in new_supports:
                known[p] = values
            evidence.append({'node': number, 'path': path, 'packet_sha256': sha(candidate.read_bytes()),
              'resolution': resolution['kind'], 'leaf_kind': resolution.get('leaf', {}).get('kind'),
              'OBBT_bounds': len(packed_obbt['b']) if packed_obbt else 0, 'Newton_steps': len(packed_newton),
              'new_supports': len(new_supports), 'candidate_math_replay': before, 'commit': committed,
              'whole_short_journal_math_replay': after, 'seconds': time.monotonic()-node_started})
            cache_history.append({'at': f'after_node{number}', **cache_state(w, oracle)})
            save('node_committed_and_mathematically_replayed')
            print(json.dumps({'node': number, 'path': path, 'resolution': evidence[-1]['leaf_kind'] or 'branch',
              'checked': committed['state']['checked'], 'seconds': time.monotonic()-started}), flush=True)
        report['all_committed_nodes_math_and_journal_replayed'] = True
        report['database_bytes'] = database.stat().st_size
        report['database_sha256'] = digest_file(database)
        report['HINTS_were_never_cleared'] = True;save('bounded_pilot_finished')
    except BaseException as error:
        report['failure'] = str(error);report['further_nodes_prohibited_after_failure'] = True;save('stopped_on_failure');raise
    finally:
        lock.close()


if __name__ == '__main__':
    main()
