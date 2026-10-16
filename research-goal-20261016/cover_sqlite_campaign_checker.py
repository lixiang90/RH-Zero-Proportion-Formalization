"""Resident independent candidate/commit gate and streaming1004-node replay.

Keeps one fixed exact-checking context, an ordered frontier and counters.
No historical record list is accumulated. Reuses frozen independent node
mathematics. Checks each transaction's complete units and expected delta;
a fresh final process streams the whole new journal from the old boundary.
"""
from pathlib import Path
import argparse, hashlib, json, os, sqlite3, sys, time, traceback
import cover_sqlite_node_replay as node

ROOT = Path(__file__).parents[1]
C = node.canon
sha = node.sha


def current_rss_bytes():
    if os.name != 'nt':
        return int(Path('/proc/self/statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE')
    import ctypes
    from ctypes import wintypes
    class Counters(ctypes.Structure):
        _fields_ = [('cb', wintypes.DWORD), ('faults', wintypes.DWORD)]+[(n, ctypes.c_size_t) for n in
          ['peak', 'working', 'peakPaged', 'paged', 'peakNonpaged', 'nonpaged', 'pagefile', 'peakPagefile']]
    c = Counters();c.cb = ctypes.sizeof(c);kernel = ctypes.WinDLL('kernel32')
    kernel.GetCurrentProcess.restype = wintypes.HANDLE;api = ctypes.WinDLL('psapi')
    api.GetProcessMemoryInfo.argtypes = [wintypes.HANDLE, ctypes.POINTER(Counters), wintypes.DWORD]
    assert api.GetProcessMemoryInfo(kernel.GetCurrentProcess(), ctypes.byref(c), c.cb)
    return c.working


def get(db, table, name):
    return node.get(db, table, name)


class Checker:
    def __init__(self, database):
        self.db = sqlite3.connect(Path(database).resolve().as_uri()+'?mode=ro', uri=True)
        self.db.execute('PRAGMA cache_size=-8192');self.db.execute('PRAGMA mmap_size=0')
        self.meta = get(self.db, 'control', 'baseline_metadata')
        self.old_epoch = get(self.db, 'control', 'pilot_epoch')
        self.epoch = get(self.db, 'control', 'campaign_epoch')
        assert self.epoch['maximum_checked'] == 133004 and self.epoch['maximum_new_nodes'] == 1000
        assert self.epoch['prefix_checked'] == 132004 and self.epoch['prefix_sequence'] == 4
        assert self.epoch['original_checked_endpoint'] == 2022500
        assert self.epoch['prefix_epoch_sha256'] == sha(C(self.old_epoch))
        self.guards = {**self.meta['input_sha256'], **self.old_epoch['source_guards'], **self.epoch['source_guards']}
        self.check_guards();assert self.meta['target'] == '11/1250'
        self.w = node.finite.low;assert [list(v) for v in self.w.root()] == self.meta['root']
        grid = ROOT/'research-goal-20261016/cover_newjet.json';assert sha(grid.read_bytes()) == self.meta['derivative_grid_sha256']
        node.finite.direction.install_grid(grid);self.table = node.finite.correlated.make_table(grid)
        self.registry = node.finite.gram.make_gram_registry();assert self.registry['sha256'] == self.meta['Gram_certificate_sha256']
        self.baseline = get(self.db, 'control', 'baseline');self.head = get(self.db, 'control', 'baseline_commit')
        assert sha(C(self.baseline)) == self.head
        self.frontier = [json.loads(r[0]) for r in self.db.execute("SELECT payload FROM entries WHERE section='unresolved' ORDER BY position")]
        assert sha(C(self.frontier)) == self.baseline['frontier_sha256']
        self.state = {k: self.meta[k] for k in ['checked', 'accepted_count', 'counts', 'unresolved_count', 'maxdepth',
          'contraction_paths', 'contraction_steps', 'sublevel_contraction_paths', 'sublevel_bounds']}
        self.state = json.loads(C(self.state));self.sequence = 0;self.pending = None
        self.counts = dict(self.baseline['section_counts']);self.totals = {'nodes': 0, 'OBBT_bounds': 0, 'Newton_steps': 0}
        self.kinds = {};self.first_Newton = None

    def check_guards(self):
        for name, expected in self.guards.items():
            assert sha((ROOT/Path(name.replace('\\', '/'))).read_bytes()) == expected, ('source guard', name)

    def expected(self, packet):
        assert self.sequence < 1004 and self.state['checked'] < 133004
        incoming = self.frontier[-1];epoch = self.old_epoch if self.sequence < 4 else self.epoch
        result = node.verify_node(packet, incoming, self.meta, epoch, self.w, self.table, self.registry)
        frontier = self.frontier[:-1]+result['children'];state = json.loads(C(self.state))
        state['checked'] += 1;state['unresolved_count'] = len(frontier);state['maxdepth'] = max(state['maxdepth'], incoming['depth'])
        resolution = packet['resolution']
        if resolution['kind'] == 'leaf':
            state['accepted_count'] += 1;state['counts'][resolution['leaf']['kind']] += 1
        if packet['OBBT'] is not None:
            state['sublevel_contraction_paths'] += 1;state['sublevel_bounds'] += result['OBBT_bounds']
        if packet['Newton']:
            state['contraction_paths'] += 1;state['contraction_steps'] += result['Newton_steps']
        digest = sha(C(packet));frontier_sha = sha(C(frontier));sequence = self.sequence+1
        committed = sha(C({'previous': self.head, 'sequence': sequence, 'node_sha256': digest,
          'frontier_sha256': frontier_sha, 'state': state}))
        return {'packet': packet, 'result': result, 'state': state, 'frontier': frontier, 'sequence': sequence,
          'packet_digest': digest, 'frontier_sha256': frontier_sha, 'previous': self.head, 'commit': committed}

    def check_units(self, transition):
        packet = transition['packet'];path = packet['path'];counts = dict(self.counts)
        supplies = [('sublevel_contractions', packet['OBBT']), ('contractions', packet['Newton'] or None)]
        r = packet['resolution'];supplies.append(('accepted' if r['kind'] == 'leaf' else 'branches', r.get('leaf', r.get('branch'))))
        for section, value in supplies:
            saved = self.db.execute('SELECT position,payload,digest FROM entries WHERE section=? AND item_key=?', (section, path)).fetchone()
            if value is None:
                assert saved is None
            else:
                assert saved and saved[0] == counts[section] and saved[1] == C(value) and sha(saved[1]) == saved[2]
                counts[section] += 1
        for support in packet['supports']:
            saved = self.db.execute("SELECT position,payload,digest FROM entries WHERE section='tangent_data' AND item_key=?", (str(support[0]),)).fetchone()
            assert saved and saved[1] == C(support) and sha(saved[1]) == saved[2]
            # Campaign producer emits only previously unseen support IDs.
            assert saved[0] == counts['tangent_data'];counts['tangent_data'] += 1
        return counts

    def accept(self, transition, stored_row):
        sequence, path, raw, wanted, previous, committed = stored_row
        assert sequence == transition['sequence'] and path == transition['packet']['path']
        assert raw == C(transition['packet']) and sha(raw) == wanted == transition['packet_digest']
        assert previous == self.head and committed == transition['commit']
        self.counts = self.check_units(transition)
        self.state = transition['state'];self.frontier = transition['frontier'];self.head = committed;self.sequence = sequence
        result = transition['result'];self.totals['nodes'] += 1
        self.totals['OBBT_bounds'] += result['OBBT_bounds'];self.totals['Newton_steps'] += result['Newton_steps']
        kind = result['resolution'];self.kinds[kind] = self.kinds.get(kind, 0)+1
        if result['Newton_steps'] and self.first_Newton is None:
            self.first_Newton = {'sequence': sequence, 'path': path, 'steps': result['Newton_steps']}
        return {'sequence': sequence, 'path': path, 'resolution': kind, 'OBBT_bounds': result['OBBT_bounds'],
          'Newton_steps': result['Newton_steps'], 'packet_sha256': wanted, 'commit': committed}

    def validate_runtime(self, exact_counts=False):
        actual = [json.loads(r[0]) for r in self.db.execute('SELECT payload FROM frontier ORDER BY position')]
        assert actual == self.frontier and get(self.db, 'runtime', 'state') == self.state
        assert get(self.db, 'runtime', 'journal_sequence') == self.sequence
        assert get(self.db, 'runtime', 'journal_commit') == self.head
        assert get(self.db, 'runtime', 'frontier_sha256') == sha(C(self.frontier))
        for section, count in self.counts.items():
            actual = self.db.execute('SELECT count(*) FROM entries WHERE section=?', (section,)).fetchone()[0] if exact_counts else (
              self.db.execute('SELECT coalesce(max(position)+1,0) FROM entries WHERE section=?', (section,)).fetchone()[0])
            assert actual == count, ('unit count', section, actual, count)
        assert self.db.execute('SELECT coalesce(max(sequence),0) FROM node_log').fetchone()[0] == self.sequence

    def replay_prefix(self, output=None):
        for row in self.db.execute('SELECT * FROM node_log WHERE sequence<=4 ORDER BY sequence'):
            result = self.accept(self.expected(json.loads(row[2])), row)
            if output:
                output.write(C(result).decode()+'\n')
        assert self.sequence == 4 and self.state['checked'] == 132004
        assert self.head == self.epoch['prefix_journal_head']

    def candidate(self, packet):
        assert self.pending is None;self.check_guards();self.pending = self.expected(packet);self.check_guards()
        r = self.pending
        return {'sequence': r['sequence'], 'packet_sha256': r['packet_digest'], 'expected_commit': r['commit'],
          'result': {k: v for k, v in r['result'].items() if k != 'children'}}

    def committed(self):
        assert self.pending is not None;self.check_guards();r = self.pending
        row = self.db.execute('SELECT * FROM node_log WHERE sequence=?', (r['sequence'],)).fetchone();assert row
        result = self.accept(r, row);self.pending = None;self.validate_runtime();self.check_guards()
        return {**result, 'state': self.state, 'frontier_sha256': sha(C(self.frontier)), 'checker_RSS_bytes': current_rss_bytes()}


def full_replay(database, receipt, node_log):
    started = time.monotonic();checker = Checker(database)
    with node_log.open('x', encoding='utf8', newline='\n') as out:
        for row in checker.db.execute('SELECT * FROM node_log ORDER BY sequence'):
            result = checker.accept(checker.expected(json.loads(row[2])), row)
            out.write(C(result).decode()+'\n')
            if checker.sequence % 100 == 0:
                print(json.dumps({'stream_replayed': checker.sequence, 'checked': checker.state['checked']}), flush=True)
    checker.validate_runtime(exact_counts=True);checker.check_guards()
    assert 4 <= checker.sequence <= 1004 and checker.state['checked'] <= 133004
    result = {'scope': __doc__, 'source_sha256': sha(Path(__file__).read_bytes()), 'passed': True,
      'journal_nodes_replayed': checker.sequence, 'new_campaign_nodes': checker.sequence-4,
      'totals': checker.totals, 'resolution_counts': checker.kinds, 'first_actual_Newton': checker.first_Newton,
      'final_state': checker.state, 'journal_head': checker.head, 'checker_RSS_bytes': current_rss_bytes(),
      'records_list_accumulated': False, 'all_OBBT_Newton_resolutions_children_and_hashes_checked': True,
      'historical_baseline_semantic_replay': False, 'full_budget_search_started': False,
      'complete_global_cover': False, 'new_zero_proportion_proven': False, 'seconds': time.monotonic()-started}
    checker.db.close();receipt.write_text(json.dumps(result, indent=2)+'\n', encoding='utf8')
    return result


def worker(database):
    checker = Checker(database);checker.replay_prefix();checker.validate_runtime()
    print(json.dumps({'ok': True, 'ready': True, 'pid': os.getpid(), 'checked': checker.state['checked'],
      'sequence': checker.sequence, 'RSS_bytes': current_rss_bytes()}), flush=True)
    for line in sys.stdin:
        request = json.loads(line);op = request['op']
        if op == 'candidate':
            result = checker.candidate(request['packet'])
        elif op == 'committed':
            result = checker.committed()
        else:
            assert op == 'shutdown' and checker.pending is None
            checker.validate_runtime();checker.db.close()
            print(json.dumps({'ok': True, 'shutdown': True}), flush=True);return
        print(json.dumps({'ok': True, 'result': result}), flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__);ap.add_argument('--database', type=Path, required=True)
    ap.add_argument('--worker', action='store_true');ap.add_argument('--receipt', type=Path);ap.add_argument('--node-log', type=Path)
    args = ap.parse_args()
    try:
        if args.worker:
            worker(args.database)
        else:
            assert args.receipt and args.node_log and not args.receipt.exists() and not args.node_log.exists()
            result = full_replay(args.database, args.receipt, args.node_log)
            print(json.dumps({'passed': True, 'nodes': result['journal_nodes_replayed'], 'seconds': result['seconds']}), flush=True)
    except BaseException as error:
        if args.worker:
            print(json.dumps({'ok': False, 'error': str(error), 'traceback': traceback.format_exc()[-16000:]}), flush=True)
        raise


if __name__ == '__main__':
    main()
