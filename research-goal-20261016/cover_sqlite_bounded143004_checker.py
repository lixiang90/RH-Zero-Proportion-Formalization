"""Independent gates for a new133004->143004 bounded epoch.

The accepted1004-node prefix is source/hash bound at resident startup.
A fresh final process still streams every<=11004 journal transition from
the original conditional frontier. No historical132000-node proof replay.
"""
from pathlib import Path
import argparse, json, os, sys, time, traceback
import cover_sqlite_campaign_checker as previous

C, sha, get = previous.C, previous.sha, previous.get


class Checker(previous.Checker):
    def __init__(self, database):
        super().__init__(database)
        self.production_epoch = get(self.db, 'control', 'bounded143004_epoch')
        e = self.production_epoch
        assert e['maximum_checked'] == 143004 and e['maximum_new_nodes'] == 10000
        assert e['prefix_checked'] == 133004 and e['prefix_sequence'] == 1004
        assert e['original_checked_endpoint'] == 2022500
        assert e['prefix_epoch_sha256'] == sha(C(self.epoch))
        self.guards.update(e['source_guards']);self.check_guards()

    def expected(self, packet):
        assert self.sequence < 11004 and self.state['checked'] < 143004
        epoch = self.old_epoch if self.sequence < 4 else self.epoch if self.sequence < 1004 else self.production_epoch
        incoming = self.frontier[-1]
        result = previous.node.verify_node(packet, incoming, self.meta, epoch, self.w, self.table, self.registry)
        frontier = self.frontier[:-1]+result['children'];state = json.loads(C(self.state))
        state['checked'] += 1;state['unresolved_count'] = len(frontier);state['maxdepth'] = max(state['maxdepth'], incoming['depth'])
        r = packet['resolution']
        if r['kind'] == 'leaf':
            state['accepted_count'] += 1;state['counts'][r['leaf']['kind']] += 1
        if packet['OBBT'] is not None:
            state['sublevel_contraction_paths'] += 1;state['sublevel_bounds'] += result['OBBT_bounds']
        if packet['Newton']:
            state['contraction_paths'] += 1;state['contraction_steps'] += result['Newton_steps']
        digest = sha(C(packet));frontier_sha = sha(C(frontier));sequence = self.sequence+1
        commit = sha(C({'previous': self.head, 'sequence': sequence, 'node_sha256': digest,
          'frontier_sha256': frontier_sha, 'state': state}))
        return {'packet': packet, 'result': result, 'state': state, 'frontier': frontier, 'sequence': sequence,
          'packet_digest': digest, 'frontier_sha256': frontier_sha, 'previous': self.head, 'commit': commit}

    def start_at_verified_prefix(self):
        e = self.production_epoch
        self.state = get(self.db, 'runtime', 'state');self.sequence = get(self.db, 'runtime', 'journal_sequence')
        self.head = get(self.db, 'runtime', 'journal_commit')
        self.frontier = [json.loads(r[0]) for r in self.db.execute('SELECT payload FROM frontier ORDER BY position')]
        self.counts = dict(self.db.execute('SELECT section,count(*) FROM entries GROUP BY section'))
        assert self.sequence == 1004 and self.state == e['prefix_state'] and self.state['checked'] == 133004
        assert self.head == e['prefix_journal_head'] and sha(C(self.frontier)) == e['prefix_frontier_sha256']
        assert self.counts == e['prefix_section_counts'];self.validate_runtime(exact_counts=True);self.check_guards()


def full_replay(database, receipt, node_log):
    started = time.monotonic();checker = Checker(database)
    with node_log.open('x', encoding='utf8', newline='\n') as out:
        for row in checker.db.execute('SELECT * FROM node_log ORDER BY sequence'):
            result = checker.accept(checker.expected(json.loads(row[2])), row)
            out.write(C(result).decode()+'\n')
            if checker.sequence == 1004:
                assert checker.head == checker.production_epoch['prefix_journal_head']
                assert checker.state == checker.production_epoch['prefix_state']
            if checker.sequence % 250 == 0:
                print(json.dumps({'stream_replayed': checker.sequence, 'checked': checker.state['checked']}), flush=True)
    checker.validate_runtime(exact_counts=True);checker.check_guards()
    assert 1004 <= checker.sequence <= 11004 and checker.state['checked'] <= 143004
    result = {'scope': __doc__, 'source_sha256': sha(Path(__file__).read_bytes()), 'passed': True,
      'journal_nodes_replayed': checker.sequence, 'new_campaign_nodes': checker.sequence-1004,
      'totals': checker.totals, 'resolution_counts': checker.kinds, 'first_actual_Newton': checker.first_Newton,
      'final_state': checker.state, 'journal_head': checker.head, 'checker_RSS_bytes': previous.current_rss_bytes(),
      'records_list_accumulated': False, 'all_OBBT_Newton_resolutions_children_and_hashes_checked': True,
      'historical_baseline_semantic_replay': False, 'full_budget_search_started': False,
      'complete_global_cover': False, 'new_zero_proportion_proven': False, 'seconds': time.monotonic()-started}
    checker.db.close();receipt.write_text(json.dumps(result, indent=2)+'\n', encoding='utf8');return result


def worker(database):
    checker = Checker(database);checker.start_at_verified_prefix()
    print(json.dumps({'ok': True, 'ready': True, 'pid': os.getpid(), 'checked': checker.state['checked'],
      'sequence': checker.sequence, 'RSS_bytes': previous.current_rss_bytes(),
      'cache_start': 'new process; historical HINTS trajectory not restored'}), flush=True)
    for line in sys.stdin:
        request = json.loads(line);op = request['op']
        if op == 'candidate':
            result = checker.candidate(request['packet'])
        elif op == 'committed':
            result = checker.committed()
        else:
            assert op == 'shutdown' and checker.pending is None
            checker.validate_runtime();checker.db.close();print(json.dumps({'ok': True, 'shutdown': True}), flush=True);return
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
