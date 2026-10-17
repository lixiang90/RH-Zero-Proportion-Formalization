"""Hard-capped10000-node SQLite campaign,133004->at most143004.

New backup only; no changes to frozen sources or prefix databases. One
resident independent checker gates every candidate and committed delta.
A fresh final process streams all<=11004 journal nodes. No cumulative
history list is kept. Stop after a durable checked node if either worker's
RSS exceeds1.5GiB. No HINTS clearing, full-budget resume or global claim.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, os, sqlite3, subprocess, sys, time
import cover_sqlite_proof_store as store
import cover_sqlite_campaign_math as math
import cover_sqlite_proof_store_test as transaction_tests

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
MAX_CHECKED = 143004
RSS_LIMIT = 3*(1<<29)
sha = lambda b: hashlib.sha256(b).hexdigest()


def digest_file(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for chunk in iter(lambda: f.read(1<<20), b''):
            h.update(chunk)
    return h.hexdigest()


def child_replay(database, receipt, log, stderr):
    command = [sys.executable, '-B', '-X', 'utf8', str(HERE/'cover_sqlite_bounded143004_checker.py'),
      '--database', str(database), '--receipt', str(receipt), '--node-log', str(log)]
    with stderr.open('x', encoding='utf8') as err:
        child = subprocess.run(command, stderr=err, text=True, encoding='utf8')
    assert child.returncode == 0, ('stream replay failed', child.returncode, str(stderr))
    result = json.loads(receipt.read_bytes());assert result['passed']
    return result


class Worker:
    def __init__(self, database, stderr):
        self.err = stderr.open('x', encoding='utf8')
        self.process = subprocess.Popen([sys.executable, '-B', '-X', 'utf8',
          str(HERE/'cover_sqlite_bounded143004_checker.py'), '--database', str(database), '--worker'],
          stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=self.err, text=True, encoding='utf8', bufsize=1)
        self.ready = self.receive();assert self.ready.get('ready') and self.ready['checked'] == 133004
    def receive(self):
        raw = self.process.stdout.readline()
        if not raw:
            raise RuntimeError(f'Independent checker ended, exit={self.process.poll()}')
        result = json.loads(raw)
        if not result.get('ok'):
            raise RuntimeError(json.dumps(result))
        return result
    def request(self, **payload):
        self.process.stdin.write(json.dumps(payload, separators=(',', ':'))+'\n');self.process.stdin.flush()
        return self.receive()
    def close(self, graceful=True):
        if self.process.poll() is None:
            if graceful:
                self.request(op='shutdown');assert self.process.wait(timeout=15) == 0
            else:
                self.process.terminate();self.process.wait(timeout=15)
        self.err.close()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-folder', type=Path, required=True)
    args = ap.parse_args();folder = args.output_folder.resolve();assert not folder.exists();folder.mkdir()
    lock = (folder/'writer.lock').open('xb')
    lock.write(store.canonical({'pid': os.getpid(), 'created_UTC': datetime.now(timezone.utc).isoformat()}));lock.flush();lock.seek(0)
    if os.name == 'nt':
        import msvcrt
        msvcrt.locking(lock.fileno(), msvcrt.LK_NBLCK, 1)
    else:
        import fcntl
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX|fcntl.LOCK_NB)
    start = time.monotonic();database = folder/'campaign.sqlite';worker = None;receipts = None;metrics = None
    report = {'scope': __doc__, 'producer_PID': os.getpid(), 'hard_stop_checked': MAX_CHECKED,
      'original_checked_endpoint': 2022500, 'RSS_limit_bytes': RSS_LIMIT, 'committed_campaign_nodes': 0,
      'new_OBBT_bounds': 0, 'new_Newton_steps': 0, 'first_actual_Newton': None,
      'historical_baseline_semantic_replay': False, 'full_budget_search_started': False,
      'complete_global_cover': False, 'new_zero_proportion_proven': False, 'process_cache_start': 'empty; no historical HINTS trajectory claim'}
    def save(stage):
        report['stage'] = stage;report['seconds'] = time.monotonic()-start
        temporary = folder/'progress.partial';temporary.write_text(json.dumps(report, indent=2)+'\n', encoding='utf8')
        temporary.replace(folder/'progress.json')
    try:
        test = transaction_tests.run(folder/'transaction-regression')
        assert test['all_passed'];(folder/'transaction-regression.json').write_text(json.dumps(test, indent=2)+'\n', encoding='utf8')
        prefix_folder = HERE/'sqlite-campaign133004';prefix_progress = json.loads((prefix_folder/'progress.json').read_bytes())
        assert prefix_progress['stage'] == 'capped_campaign_and_full_new_journal_replay_finished' and prefix_progress['committed_campaign_nodes'] == 1000
        source_path = prefix_folder/'campaign.sqlite';assert digest_file(source_path) == prefix_progress['database_sha256']
        source = sqlite3.connect(source_path.resolve().as_uri()+'?mode=ro', uri=True);dest = store.connect(database)
        source.backup(dest, pages=512);source.close();assert dest.execute('PRAGMA integrity_check').fetchone()[0] == 'ok'
        meta = store.get(dest, 'control', 'baseline_metadata');old_epoch = store.get(dest, 'control', 'campaign_epoch'); pilot_epoch = store.get(dest, 'control', 'pilot_epoch')
        assert store.get(dest, 'runtime', 'state')['checked'] == 133004
        assert store.get(dest, 'runtime', 'journal_sequence') == 1004
        head = store.get(dest, 'runtime', 'journal_commit');assert head == prefix_progress['journal_head']
        paths = [Path(__file__), HERE/'cover_sqlite_campaign_math.py', HERE/'cover_sqlite_bounded143004_checker.py',
          HERE/'cover_sqlite_proof_store.py', HERE/'cover_sqlite_proof_store_test.py', HERE/'cover_sqlite_node_replay.py']
        guards = {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in paths}
        epoch = {'schema': 'sqlite-bounded10000-133004-143004-v1', 'maximum_checked': MAX_CHECKED, 'maximum_new_nodes': 10000,
          'prefix_checked': 133004, 'prefix_sequence': 1004, 'prefix_journal_head': head,
          'prefix_epoch_sha256': sha(store.canonical(old_epoch)), 'prefix_database_sha256': prefix_progress['database_sha256'],
          'prefix_manifest_sha256': sha((HERE/'cover-sqlite-campaign133004-files.json').read_bytes()),
          'original_checked_endpoint': 2022500, 'source_guards': guards, 'target': '11/1250',
          'RSS_limit_bytes': RSS_LIMIT, 'single_writer_lock': str((folder/'writer.lock').relative_to(ROOT)),
          'not_full_budget_resume': True,
          'prefix_state': store.get(dest, 'runtime', 'state'),
          'prefix_frontier_sha256': store.get(dest, 'runtime', 'frontier_sha256'),
          'prefix_section_counts': dict(dest.execute('SELECT section,count(*) FROM entries GROUP BY section')),
          'cache_start': 'new process empty caches; historical HINTS is not restored',
          'original_HINTS_trajectory_continuation': False,
          'host_prelaunch_check': {'method': 'require_escalated Get-CimInstance Win32_Process', 'matching_old_producers': 0, 'check_exit_code': 0}}
        all_guards = {**meta['input_sha256'], **pilot_epoch['source_guards'], **old_epoch['source_guards'], **guards}
        store.check_guards(ROOT, all_guards)
        dest.execute('BEGIN IMMEDIATE');store.put(dest, 'control', 'bounded143004_epoch', epoch);dest.execute('COMMIT');dest.close()
        (folder/'epoch.json').write_bytes(store.canonical(epoch)+b'\n')
        report['epoch_sha256'] = sha(store.canonical(epoch));report['prefix_database_sha256'] = prefix_progress['database_sha256']
        save('transaction_regression_and_backup_complete')
        preflight = child_replay(database, folder/'prefix-stream-replay.json', folder/'prefix-stream-nodes.jsonl', folder/'prefix-stream.stderr.log')
        assert preflight['journal_nodes_replayed'] == 1004
        worker = Worker(database, folder/'resident-checker.stderr.log')
        report['checker_PID'] = worker.ready['pid'];report['checker_start_RSS_bytes'] = worker.ready['RSS_bytes']
        inherited = math.inherited;w = math.w;g = math.g;grid = HERE/'cover_newjet.json'
        assert inherited.direction.install_grid(grid) == meta['derivative_grid_sha256']
        oracle = inherited.correlated.make_correlated_oracle(grid)
        registry = inherited.gram.make_gram_registry();engine = inherited.obbt.make_engine(w)
        known = {};db = store.connect(database, readonly=True)
        for key, payload in db.execute("SELECT item_key,payload FROM entries WHERE section='tangent_data' ORDER BY position"):
            p, *values = json.loads(payload);assert key == str(p) and p not in known
            known[p] = values;w.USED_SUPPORTS.add(p)
        db.close();assert len(known) == 2540
        report['supports_loaded'] = len(known);report['initial_cache'] = inherited.cache_state(w, oracle)
        receipts = (folder/'node-gates.jsonl').open('x', encoding='utf8', newline='\n')
        metrics = (folder/'metrics.jsonl').open('x', encoding='utf8', newline='\n')
        save('resident_checker_ready_before_new_nodes')
        print(json.dumps({'producer_PID': os.getpid(), 'checker_PID': worker.ready['pid'], 'hard_stop': MAX_CHECKED}), flush=True)
        while True:
            store.check_guards(ROOT, all_guards)
            db = store.connect(database, readonly=True);current = store.get(db, 'runtime', 'state')
            top = db.execute('SELECT payload FROM frontier ORDER BY position DESC LIMIT 1').fetchone()
            frontier_sha = store.get(db, 'runtime', 'frontier_sha256');db.close()
            if current['checked'] >= MAX_CHECKED:
                report['stop_reason'] = 'hard_checked_cap';break
            if top is None:
                report['stop_reason'] = 'empty_frontier';break
            incoming = json.loads(top[0]);packet = math.discover(incoming, oracle, registry, engine, known, report['epoch_sha256'])
            gate = worker.request(op='candidate', packet=packet)['result']
            assert gate['packet_sha256'] == sha(store.canonical(packet))
            store.check_guards(ROOT, all_guards)
            committed = store.append_node(database, packet, ROOT, expected_frontier_sha256=frontier_sha)
            delta = worker.request(op='committed')['result']
            assert committed['commit'] == gate['expected_commit'] == delta['commit']
            assert committed['state'] == delta['state'] and committed['frontier_sha256'] == delta['frontier_sha256']
            store.check_guards(ROOT, all_guards)
            for p, *values in packet['supports']:
                known[p] = values
            report['committed_campaign_nodes'] += 1;report['new_OBBT_bounds'] += delta['OBBT_bounds'];report['new_Newton_steps'] += delta['Newton_steps']
            if delta['Newton_steps'] and report['first_actual_Newton'] is None:
                report['first_actual_Newton'] = {k: delta[k] for k in ['sequence', 'path', 'Newton_steps']}
                print(json.dumps({'first_actual_Newton': report['first_actual_Newton']}), flush=True)
            producer_rss = math.current_rss_bytes();report['producer_RSS_bytes'] = producer_rss
            report['checker_RSS_bytes'] = delta['checker_RSS_bytes'];report['state'] = committed['state'];report['journal_head'] = committed['commit']
            receipts.write(store.canonical({'candidate': gate, 'committed': delta}).decode()+'\n');receipts.flush()
            n = report['committed_campaign_nodes']
            if n == 1 or n % 25 == 0:
                record = {'new_nodes': n, 'checked': current['checked']+1, 'producer_RSS_bytes': producer_rss,
                  'checker_RSS_bytes': delta['checker_RSS_bytes'], 'cache': inherited.cache_state(w, oracle)}
                metrics.write(store.canonical(record).decode()+'\n');metrics.flush();report['latest_cache'] = record['cache']
                save('verified_durable_node_boundary')
                print(json.dumps({'checked': report['state']['checked'], 'new_nodes': n,
                  'Newton_steps': report['new_Newton_steps'], 'RSS_MiB': round(producer_rss/(1<<20), 2),
                  'seconds': time.monotonic()-start}), flush=True)
            if max(producer_rss, delta['checker_RSS_bytes']) > RSS_LIMIT:
                report['stop_reason'] = 'graceful_RSS_limit_after_verified_durable_node';break
        worker.close();worker = None;receipts.close();receipts = None;metrics.close();metrics = None
        save('discovery_stopped_before_final_stream_replay')
        final = child_replay(database, folder/'final-stream-replay.json', folder/'final-stream-nodes.jsonl', folder/'final-stream.stderr.log')
        assert final['new_campaign_nodes'] == report['committed_campaign_nodes']
        assert final['final_state'] == report['state'] and final['journal_head'] == report['journal_head']
        report['final_stream_replay_passed'] = True;report['final_state'] = final['final_state']
        report['database_bytes'] = database.stat().st_size;report['database_sha256'] = digest_file(database)
        report['HINTS_were_never_cleared'] = True;report['final_cache'] = inherited.cache_state(w, oracle)
        save('capped_campaign_and_full_new_journal_replay_finished')
    except BaseException as error:
        report['failure'] = str(error);report['further_nodes_prohibited_after_failure'] = True;save('stopped_on_guard_or_math_failure');raise
    finally:
        if worker is not None:
            worker.close(graceful=False)
        if receipts is not None:
            receipts.close()
        if metrics is not None:
            metrics.close()
        lock.close()


if __name__ == '__main__':
    main()
