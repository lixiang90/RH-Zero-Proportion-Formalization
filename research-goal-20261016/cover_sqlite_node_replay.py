"""Independent per-node mathematics and <=4-node SQLite journal replay.

Uses the frozen independent OBBT/Newton/flow/scalar verifiers, not producer
selection or optimization. Baseline frontier is a conditional starting
boundary: the132000-node historical baseline is not semantically replayed
here. Check candidate before commit and all committed transitions afterward.
"""
from pathlib import Path
import argparse, hashlib, json, sqlite3, time
import window_compact_obbt_replay as finite

ROOT = Path(__file__).parents[1]
sha = lambda b: hashlib.sha256(b).hexdigest()


def canon(v):
    return json.dumps(v, sort_keys=True, ensure_ascii=True, allow_nan=False, separators=(',', ':')).encode('ascii')


def get(db, table, name):
    row = db.execute(f'SELECT payload FROM {table} WHERE name=?', (name,)).fetchone();assert row
    return json.loads(row[0])


def setup(db):
    meta = get(db, 'control', 'baseline_metadata');epoch = get(db, 'control', 'pilot_epoch')
    assert epoch['maximum_nodes'] == 4 and epoch['baseline_checked'] == 132000
    assert epoch['baseline_source_sha256'] == '2e50e2303ca3705ae9ba91e741764e84550c382049b88ae5cbd064247bba671d'
    for name, expected in {**meta['input_sha256'], **epoch['source_guards']}.items():
        assert sha((ROOT/Path(name.replace('\\', '/'))).read_bytes()) == expected, name
    assert meta['target'] == '11/1250'
    w = finite.low;g = w.g
    assert [list(v) for v in w.root()] == meta['root']
    grid = ROOT/'research-goal-20261016/cover_newjet.json'
    assert sha(grid.read_bytes()) == meta['derivative_grid_sha256']
    finite.direction.install_grid(grid);table = finite.correlated.make_table(grid)
    registry = finite.gram.make_gram_registry();assert registry['sha256'] == meta['Gram_certificate_sha256']
    return meta, epoch, w, table, registry


def verify_node(packet, incoming, meta, epoch, w, table, registry):
    g = w.g;state = [list(v) for v in incoming['state']]
    finite.newton.a.closure_valid(state)
    assert packet['path'] == incoming['path'] and packet['depth'] == incoming['depth']
    assert packet['incoming_cell_sha256'] == sha(canon(state))
    assert packet['epoch_sha256'] == sha(canon(epoch))
    for support in packet['supports']:
        p, *values = support;assert isinstance(p, int) and values == list(w.original_support(p))
    counts = {'OBBT_bounds': 0, 'Newton_steps': 0, 'implicit_empty_children': 0}
    if packet['OBBT'] is not None:
        decoded = finite.codec.unpack_obbt(state, packet['OBBT'], g.TARGET, w)
        counts['OBBT_bounds'] = len(decoded['certificates'])
        state = finite.obbt.verify_step(state, decoded, g.TARGET)
    if packet['Newton']:
        assert state is not None
        for packed in packet['Newton']:
            assert state is not None
            decoded = finite.codec.unpack_newton(state, packed, w)
            state = finite.newton.verify_step(state, decoded, w.P, table);counts['Newton_steps'] += 1
    resolution = packet['resolution']
    if state is None:
        assert resolution['kind'] == 'leaf'
        leaf = resolution['leaf'];expected = 'stationary_empty' if packet['Newton'] else 'sublevel_empty'
        assert leaf['kind'] == expected and leaf['path'] == incoming['path'] and leaf['depth'] == incoming['depth']
        return {**counts, 'resolution': expected, 'children': []}
    lo, hi = state
    if resolution['kind'] == 'branch':
        branch = resolution['branch'];ax = branch['axis'];cut = branch['cut']
        assert branch['path'] == incoming['path'] and isinstance(ax, int) and 0 <= ax < 45
        assert lo[ax] < cut < hi[ax];children = []
        for bit, upper in [('1', False), ('0', True)]:
            child = finite.newton.a.child(state, ax, cut, upper)
            if child is None:
                counts['implicit_empty_children'] += 1
            else:
                children.append({'path': incoming['path']+bit, 'depth': incoming['depth']+1, 'state': child})
        assert canon(children) == canon(resolution['children'])
        return {**counts, 'resolution': 'branch', 'children': children}
    assert resolution['kind'] == 'leaf'
    row = finite.codec.unpack_leaf(state, resolution['leaf'], w);kind = row['kind']
    assert row['path'] == incoming['path'] and row['depth'] == incoming['depth']
    if kind == 'reflection':
        assert hi[8] < lo[0]
    elif kind == 'Gram':
        finite.gram.verify(state, row['result'], meta['target'], registry)
    elif kind == 'stationary':
        rec = row['result']
        if isinstance(rec['direction'], list):
            assert rec['derivative_grid_sha256'] == meta['derivative_grid_sha256']
            if rec.get('kind') == 'correlated_direction':
                finite.correlated.verify(state, rec, w.P, table)
            else:
                d = rec['direction'];assert len(d) == 9 and all(isinstance(v, int) for v in d)
                assert all(v >= 0 or lo[i] > g.SEP for i, v in enumerate(d))
                value = finite.direction.upper(d, finite.direction.ranges(state))
                assert value < 0 and str(value) == rec['upper_numerator']
                assert rec['denominator'] == str(g.D*finite.direction.w.DS)
        else:
            r = rec['coordinate'];dr = rec['direction'];lower = upper = g.BS[r]*w.DS
            for i, j, a in g.TERMS:
                if i <= r < j:
                    z = g.LOOK[i, j];dl, du = w.derivative_range(lo[z], hi[z]);lower += a*dl;upper += a*du
            if dr == 1:
                assert upper < 0 and str(upper) == rec['gradient_upper']
            else:
                assert dr == -1 and lo[r] > g.SEP and lower > 0 and str(lower) == rec['gradient_lower']
    else:
        assert kind == 'value';rec = row['result'];cert = rec['certificate']
        assert cert['lower_bounds'] == lo and cert['upper_bounds'] == hi and cert['mixture_denominator'] == g.LD
        mass = [0]*len(g.TERMS);C = 0;coeff = [b*g.LD for b in g.BS]
        for t, p, weight0, const0, slope0 in cert['mixture']:
            weight, const, slope = map(int, [weight0, const0, slope0]);assert weight > 0
            i, j, a = g.TERMS[t];z = g.LOOK[i, j];l, u = lo[z], hi[z]
            if p == -1:
                assert slope == 0 and const == w.constant_lower(l, u)*g.SC
            else:
                assert p >= 0;pl, pu, v, sl, err = w.original_support(p)
                assert pl <= l and u <= pu and const == g.SC*v-10*sl*p-10*err*max(p-l, 0) and slope == 10*sl
            mass[t] += weight;C += weight*const
            for r in range(i, j):
                coeff[r] += weight*slope
        assert all(m <= a*(g.LD//g.D) for m, (_, _, a) in zip(mass, g.TERMS))
        assert str(C) == cert['intercept'] and list(map(str, coeff)) == cert['gap_coefficients']
        flow = cert['flow'];balance = [0]*10;cost = 0
        for i, j, y0, u in flow['nonzero_flow']:
            y = int(y0);assert y >= 0 and i != j and u == finite.newton.a.edge_value(state, i, j)
            balance[i] += y;balance[j] -= y;cost += y*u
        desired = [-coeff[0]]+[coeff[i-1]-coeff[i] for i in range(1, 9)]+[coeff[-1]]
        assert balance == desired == list(map(int, flow['divergence'])) and cost == int(flow['cost'])
        assert C-cost == int(rec['floor_numerator']) and C-cost >= g.TARGET
    return {**counts, 'resolution': kind, 'children': []}


def verify_journal(db, meta, epoch, w, table, registry):
    frontier = [json.loads(row[0]) for row in db.execute("SELECT payload FROM entries WHERE section='unresolved' ORDER BY position")]
    state = {k: meta[k] for k in ['checked', 'accepted_count', 'counts', 'unresolved_count', 'maxdepth',
      'contraction_paths', 'contraction_steps', 'sublevel_contraction_paths', 'sublevel_bounds']}
    state = json.loads(canon(state));previous = get(db, 'control', 'baseline_commit');records = []
    baseline = get(db, 'control', 'baseline');assert sha(canon(baseline)) == previous
    assert sha(canon(frontier)) == baseline['frontier_sha256'];sequence = 0
    for seq, path, raw, wanted, before, committed in db.execute('SELECT * FROM node_log ORDER BY sequence'):
        sequence += 1;assert seq == sequence <= 4 and before == previous and sha(raw) == wanted
        packet = json.loads(raw);incoming = frontier.pop();assert path == incoming['path']
        result = verify_node(packet, incoming, meta, epoch, w, table, registry)
        for section, value in [('sublevel_contractions', packet['OBBT']), ('contractions', packet['Newton'] or None)]:
            stored = db.execute('SELECT payload FROM entries WHERE section=? AND item_key=?', (section, path)).fetchone()
            assert (stored is None) if value is None else stored is not None and stored[0] == canon(value)
        resolution = packet['resolution'];section = 'accepted' if resolution['kind'] == 'leaf' else 'branches'
        value = resolution['leaf'] if section == 'accepted' else resolution['branch']
        stored = db.execute('SELECT payload FROM entries WHERE section=? AND item_key=?', (section, path)).fetchone()
        assert stored and stored[0] == canon(value)
        for support in packet['supports']:
            stored = db.execute("SELECT payload FROM entries WHERE section='tangent_data' AND item_key=?", (str(support[0]),)).fetchone()
            assert stored and stored[0] == canon(support)
        frontier.extend(result['children']);state['checked'] += 1;state['unresolved_count'] = len(frontier)
        state['maxdepth'] = max(state['maxdepth'], incoming['depth'])
        if resolution['kind'] == 'leaf':
            state['accepted_count'] += 1;state['counts'][value['kind']] += 1
        if packet['OBBT'] is not None:
            state['sublevel_contraction_paths'] += 1;state['sublevel_bounds'] += result['OBBT_bounds']
        if packet['Newton']:
            state['contraction_paths'] += 1;state['contraction_steps'] += result['Newton_steps']
        expected = sha(canon({'previous': previous, 'sequence': seq, 'node_sha256': wanted,
          'frontier_sha256': sha(canon(frontier)), 'state': state}))
        assert expected == committed;previous = committed;records.append({'path': path, **result})
    stored_frontier = [json.loads(r[0]) for r in db.execute('SELECT payload FROM frontier ORDER BY position')]
    assert frontier == stored_frontier and state == get(db, 'runtime', 'state')
    assert sequence == get(db, 'runtime', 'journal_sequence') and previous == get(db, 'runtime', 'journal_commit')
    assert sha(canon(frontier)) == get(db, 'runtime', 'frontier_sha256')
    expected_counts = {'accepted': state['accepted_count'], 'branches': state['checked']-state['accepted_count'],
      'contractions': state['contraction_paths'], 'sublevel_contractions': state['sublevel_contraction_paths'],
      'unresolved': baseline['section_counts']['unresolved']}
    for section, count in expected_counts.items():
        assert db.execute('SELECT count(*) FROM entries WHERE section=?', (section,)).fetchone()[0] == count
    return {'nodes': sequence, 'records': records, 'state': state, 'journal_head': previous,
      'all_node_mathematics_and_child_geometry_passed': True, 'journal_chain_and_runtime_counters_matched': True}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--database', type=Path, required=True);ap.add_argument('--candidate', type=Path)
    ap.add_argument('--receipt', type=Path, required=True);args = ap.parse_args();assert not args.receipt.exists()
    started = time.monotonic();db = sqlite3.connect(args.database.resolve().as_uri()+'?mode=ro', uri=True)
    db.execute('PRAGMA cache_size=-8192');db.execute('PRAGMA mmap_size=0')
    meta, epoch, w, table, registry = setup(db)
    if args.candidate:
        raw = args.candidate.read_bytes();packet = json.loads(raw)
        row = db.execute('SELECT payload FROM frontier ORDER BY position DESC LIMIT 1').fetchone();assert row
        result = {'candidate_sha256': sha(raw), 'result': verify_node(packet, json.loads(row[0]), meta, epoch, w, table, registry)}
    else:
        result = verify_journal(db, meta, epoch, w, table, registry)
    db.close();out = {'scope': __doc__, 'script_sha256': sha(Path(__file__).read_bytes()), 'passed': True,
      'candidate_only': args.candidate is not None, 'result': result,
      'historical_baseline_semantic_replay': False, 'actual_Lean_new_node_theorems_compiled': False,
      'complete_global_cover': False, 'new_zero_proportion_proven': False, 'seconds': time.monotonic()-started}
    args.receipt.write_text(json.dumps(out, indent=2)+'\n', encoding='utf8')
    print(json.dumps({'passed': True, 'candidate': args.candidate is not None, 'seconds': out['seconds']}), flush=True)


if __name__ == '__main__':
    main()
