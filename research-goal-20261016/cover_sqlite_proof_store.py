"""Bounded-memory SQLite proof-store prototype; no search or mathematics.

Stream one immutable-open compact-v2 JSON snapshot into a single ACID
baseline transaction. Retain each complete canonical JSON unit, its hash,
collection order, all metadata and ordered frontier. Publish only after
commit. A separate append_node transaction stores supports/witnesses and
frontier/counters together. Mathematical verification remains the caller's
obligation. This module does not adopt or restart any producer.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, os, sqlite3, time
from cover_compact_checkpoint import Stream

SCHEMA = 'RelevantBelow-KKT-OBBT-SQLite-prototype-v1'
COLLECTIONS = {'accepted': 'array', 'branches': 'array', 'contractions': 'map',
               'sublevel_contractions': 'map', 'tangent_data': 'array', 'unresolved': 'frontier'}
sha = lambda b: hashlib.sha256(b).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=True, allow_nan=False,
                      separators=(',', ':')).encode('ascii')


def peak_working_set_bytes():
    if os.name != 'nt':
        import resource
        return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024
    import ctypes
    from ctypes import wintypes
    class Counters(ctypes.Structure):
        _fields_ = [('cb', wintypes.DWORD), ('PageFaultCount', wintypes.DWORD)]+[
          (name, ctypes.c_size_t) for name in ['PeakWorkingSetSize', 'WorkingSetSize',
          'QuotaPeakPagedPoolUsage', 'QuotaPagedPoolUsage', 'QuotaPeakNonPagedPoolUsage',
          'QuotaNonPagedPoolUsage', 'PagefileUsage', 'PeakPagefileUsage']]
    c = Counters();c.cb = ctypes.sizeof(c)
    kernel = ctypes.WinDLL('kernel32');kernel.GetCurrentProcess.restype = wintypes.HANDLE
    psapi = ctypes.WinDLL('psapi');psapi.GetProcessMemoryInfo.argtypes = [wintypes.HANDLE, ctypes.POINTER(Counters), wintypes.DWORD]
    assert psapi.GetProcessMemoryInfo(kernel.GetCurrentProcess(), ctypes.byref(c), c.cb)
    return c.PeakWorkingSetSize


def connect(path, readonly=False):
    if readonly:
        return sqlite3.connect(Path(path).resolve().as_uri()+'?mode=ro', uri=True)
    db = sqlite3.connect(path, isolation_level=None)
    db.execute('PRAGMA journal_mode=DELETE')
    db.execute('PRAGMA synchronous=FULL')
    db.execute('PRAGMA cache_size=-8192')
    db.execute('PRAGMA temp_store=FILE')
    db.execute('PRAGMA mmap_size=0')
    db.execute('PRAGMA foreign_keys=ON')
    return db


def check_guards(root, guards):
    root = Path(root).resolve()
    for name, expected in guards.items():
        relative = Path(name.replace('\\', '/'))
        assert not relative.is_absolute() and '..' not in relative.parts
        source = root/relative
        assert sha(source.read_bytes()) == expected, ('source guard mismatch', name)


def schema(db):
    statements = [
      'CREATE TABLE control(name TEXT PRIMARY KEY, payload BLOB NOT NULL)',
      'CREATE TABLE fields(position INTEGER PRIMARY KEY, name TEXT NOT NULL UNIQUE, kind TEXT NOT NULL)',
      'CREATE TABLE metadata(name TEXT PRIMARY KEY, payload BLOB NOT NULL, digest TEXT NOT NULL)',
      'CREATE TABLE entries(section TEXT NOT NULL, position INTEGER NOT NULL, item_key TEXT NOT NULL, payload BLOB NOT NULL, digest TEXT NOT NULL, PRIMARY KEY(section,position), UNIQUE(section,item_key))',
      'CREATE TABLE frontier(position INTEGER PRIMARY KEY, path TEXT NOT NULL UNIQUE, payload BLOB NOT NULL, digest TEXT NOT NULL)',
      'CREATE TABLE node_log(sequence INTEGER PRIMARY KEY, path TEXT NOT NULL UNIQUE, payload BLOB NOT NULL, digest TEXT NOT NULL, previous_commit TEXT NOT NULL, commit_digest TEXT NOT NULL)',
      'CREATE TABLE runtime(name TEXT PRIMARY KEY, payload BLOB NOT NULL)']
    for statement in statements:
        db.execute(statement)


def put(db, table, name, value):
    assert table in ['control', 'runtime']
    db.execute(f'INSERT OR REPLACE INTO {table}(name,payload) VALUES(?,?)', (name, canonical(value)))


def get(db, table, name):
    assert table in ['control', 'runtime', 'metadata']
    row = db.execute(f'SELECT payload FROM {table} WHERE name=?', (name,)).fetchone()
    assert row is not None, (table, name)
    return json.loads(row[0])


def frontier_digest(db):
    h = hashlib.sha256();h.update(b'[');first = True
    for payload, digest in db.execute('SELECT payload,digest FROM frontier ORDER BY position'):
        assert sha(payload) == digest
        if not first:
            h.update(b',')
        first = False;h.update(payload)
    h.update(b']');return h.hexdigest()


def entry_key(section, value):
    if section in ['accepted', 'branches', 'unresolved']:
        assert isinstance(value, dict) and isinstance(value['path'], str)
        return value['path']
    assert section == 'tangent_data' and isinstance(value, list) and value
    assert isinstance(value[0], int)
    return str(value[0])


def import_snapshot(source, output, root, *, expected_source_sha256=None):
    source = Path(source);output = Path(output)
    assert source.resolve() != output.resolve() and not output.exists()
    building = output.with_name(output.name+'.building');assert not building.exists()
    started = time.monotonic();stream = Stream(source);db = connect(building)
    encoded = hashlib.sha256();counts = {};sizes = {};largest = 0;metadata = {}
    try:
        db.execute('BEGIN IMMEDIATE');schema(db);put(db, 'control', 'schema', SCHEMA)
        stream.token('{');encoded.update(b'{');top = 0
        while stream.peek() != '}':
            if top:
                encoded.update(b',')
            name = stream.value();assert isinstance(name, str);stream.token(':')
            kind = COLLECTIONS.get(name, 'metadata')
            db.execute('INSERT INTO fields VALUES(?,?,?)', (top, name, kind))
            encoded.update(canonical(name)+b':');top += 1
            if kind == 'metadata':
                value = stream.value();payload = canonical(value)
                assert len(payload) <= 4<<20, ('unexpected large metadata', name)
                db.execute('INSERT INTO metadata VALUES(?,?,?)', (name, payload, sha(payload)))
                metadata[name] = value;encoded.update(payload)
            else:
                opening, closing = ('{', '}') if kind == 'map' else ('[', ']')
                stream.token(opening);encoded.update(opening.encode());position = 0
                total_bytes = 0
                while stream.peek() != closing:
                    if position:
                        encoded.update(b',')
                    key = stream.value() if kind == 'map' else None
                    if kind == 'map':
                        assert isinstance(key, str);stream.token(':');encoded.update(canonical(key)+b':')
                    value = stream.value();payload = canonical(value)
                    key = entry_key(name, value) if key is None else key
                    if kind == 'frontier':
                        db.execute('INSERT INTO frontier VALUES(?,?,?,?)', (position, key, payload, sha(payload)))
                    # The baseline frontier remains immutable in entries;
                    # frontier is its live, transactional working copy.
                    db.execute('INSERT INTO entries VALUES(?,?,?,?,?)', (name, position, key, payload, sha(payload)))
                    encoded.update(payload);total_bytes += len(payload);largest = max(largest, len(payload));position += 1
                    if stream.peek() != ',':
                        break
                    stream.token(',')
                stream.token(closing);encoded.update(closing.encode());counts[name] = position;sizes[name] = total_bytes
            if stream.peek() != ',':
                break
            stream.token(',')
        stream.token('}');encoded.update(b'}');assert stream.peek() == ''
        stream.file.close()
        assert metadata['format'] == 'RelevantBelow-KKT-OBBT-compact-v2'
        assert metadata['accepted_count'] == counts['accepted']
        assert metadata['unresolved_count'] == counts['unresolved']
        assert metadata['checked'] == counts['accepted']+counts['branches']
        assert counts['contractions'] == metadata['contraction_paths']
        assert counts['sublevel_contractions'] == metadata['sublevel_contraction_paths']
        check_guards(root, metadata['input_sha256'])
        original_sha = stream.sha.hexdigest()
        if expected_source_sha256 is not None:
            assert original_sha == expected_source_sha256
        baseline = {'source_path': str(source), 'source_bytes': stream.size,
          'source_sha256': original_sha, 'canonical_document_sha256': encoded.hexdigest(),
          'section_counts': counts, 'section_canonical_payload_bytes': sizes,
          'largest_canonical_unit_bytes': largest, 'frontier_sha256': frontier_digest(db),
          'checked': metadata['checked'], 'schema': SCHEMA}
        baseline_commit = sha(canonical(baseline))
        put(db, 'control', 'baseline', baseline);put(db, 'control', 'baseline_commit', baseline_commit)
        put(db, 'control', 'baseline_metadata', metadata)
        put(db, 'control', 'published_after_complete_baseline_commit', True)
        state = {k: metadata[k] for k in ['checked', 'accepted_count', 'counts', 'unresolved_count',
          'maxdepth', 'contraction_paths', 'contraction_steps', 'sublevel_contraction_paths', 'sublevel_bounds']}
        put(db, 'runtime', 'state', state);put(db, 'runtime', 'journal_sequence', 0)
        put(db, 'runtime', 'journal_commit', baseline_commit)
        put(db, 'runtime', 'frontier_sha256', baseline['frontier_sha256'])
        db.execute('COMMIT');db.close()
        assert not output.exists();building.rename(output)
    except BaseException:
        try:
            db.execute('ROLLBACK')
        except sqlite3.Error:
            pass
        db.close();stream.file.close();raise
    receipt = {'scope': __doc__, 'source_sha256': sha(Path(__file__).read_bytes()),
      'database_path': str(output), 'database_bytes': output.stat().st_size,
      'baseline': baseline, 'baseline_commit': baseline_commit,
      'SQLite_cache_KiB': 8192, 'SQLite_temp_store_FILE': True,
      'process_peak_working_set_bytes': peak_working_set_bytes(),
      'entire_history_loaded_in_memory': False, 'baseline_semantic_replay': False,
      'new_search_or_restart_started': False, 'new_zero_proportion_proven': False,
      'seconds': time.monotonic()-started}
    return receipt


class InjectedCrash(RuntimeError):
    pass


def append_node(database, packet, root, *, expected_frontier_sha256,
                fault_at=None, hard_crash_at=None):
    """One-node storage transaction, with mathematical soundness as input.

    packet has path/depth/incoming_cell_sha256/supports/OBBT/Newton and
    resolution. A resolution is {'kind':'leaf','leaf':packed_leaf} or
    {'kind':'branch','branch':branch_record,'children':[ordered_frontier_rows]}.
    This interface checks storage identities/counters/guards, not the
    mathematical correctness of supplied contractions or child geometry.
    Fault hooks are for the isolated toy database only.
    """
    db = connect(database)
    def crash(stage):
        if hard_crash_at == stage:
            os._exit(77)
        if fault_at == stage:
            raise InjectedCrash(stage)
    try:
        db.execute('BEGIN IMMEDIATE')
        assert get(db, 'control', 'schema') == SCHEMA
        baseline = get(db, 'control', 'baseline_metadata');guards = baseline['input_sha256']
        check_guards(root, guards)
        assert frontier_digest(db) == get(db, 'runtime', 'frontier_sha256') == expected_frontier_sha256
        top = db.execute('SELECT position,path,payload,digest FROM frontier ORDER BY position DESC LIMIT 1').fetchone()
        assert top is not None
        position, path, payload, digest = top;old = json.loads(payload);assert sha(payload) == digest
        assert packet['path'] == path and packet['depth'] == old['depth']
        assert packet['incoming_cell_sha256'] == sha(canonical(old['state']))
        assert not db.execute('SELECT 1 FROM node_log WHERE path=?', (path,)).fetchone()
        assert not db.execute("SELECT 1 FROM entries WHERE section IN ('accepted','branches') AND item_key=?", (path,)).fetchone()
        def insert(section, key, value):
            encoded = canonical(value)
            prior = db.execute('SELECT payload FROM entries WHERE section=? AND item_key=?', (section, key)).fetchone()
            if prior is not None:
                assert section == 'tangent_data' and prior[0] == encoded
                return
            n = db.execute('SELECT coalesce(max(position)+1,0) FROM entries WHERE section=?', (section,)).fetchone()[0]
            db.execute('INSERT INTO entries VALUES(?,?,?,?,?)', (section, n, key, encoded, sha(encoded)))
        for support in packet['supports']:
            insert('tangent_data', entry_key('tangent_data', support), support)
        if packet['OBBT'] is not None:
            insert('sublevel_contractions', path, packet['OBBT'])
        if packet['Newton']:
            insert('contractions', path, packet['Newton'])
        resolution = packet['resolution'];assert resolution['kind'] in ['leaf', 'branch']
        if resolution['kind'] == 'leaf':
            leaf = resolution['leaf'];assert leaf['path'] == path and leaf['depth'] == old['depth']
            insert('accepted', path, leaf)
        else:
            branch = resolution['branch'];assert branch['path'] == path
            insert('branches', path, branch)
        crash('after_witnesses')
        db.execute('DELETE FROM frontier WHERE position=?', (position,))
        if resolution['kind'] == 'branch':
            children = resolution['children'];assert len(children) <= 2
            assert [r['path'] for r in children] in [[path+'1', path+'0'], [path+'1'], [path+'0'], []]
            for child in children:
                assert child['depth'] == old['depth']+1
                encoded = canonical(child);db.execute('INSERT INTO frontier VALUES(?,?,?,?)',
                  (position, child['path'], encoded, sha(encoded)));position += 1
        state = get(db, 'runtime', 'state');state['checked'] += 1
        state['maxdepth'] = max(state['maxdepth'], old['depth'])
        if resolution['kind'] == 'leaf':
            state['accepted_count'] += 1;state['counts'][resolution['leaf']['kind']] += 1
        if packet['OBBT'] is not None:
            state['sublevel_contraction_paths'] += 1;state['sublevel_bounds'] += len(packet['OBBT']['b'])
        if packet['Newton']:
            state['contraction_paths'] += 1;state['contraction_steps'] += len(packet['Newton'])
        state['unresolved_count'] = db.execute('SELECT count(*) FROM frontier').fetchone()[0]
        put(db, 'runtime', 'state', state);new_frontier = frontier_digest(db)
        put(db, 'runtime', 'frontier_sha256', new_frontier)
        sequence = get(db, 'runtime', 'journal_sequence')+1;previous = get(db, 'runtime', 'journal_commit')
        encoded = canonical(packet);unit_sha = sha(encoded)
        commit = sha(canonical({'previous': previous, 'sequence': sequence,
          'node_sha256': unit_sha, 'frontier_sha256': new_frontier, 'state': state}))
        db.execute('INSERT INTO node_log VALUES(?,?,?,?,?,?)', (sequence, path, encoded, unit_sha, previous, commit))
        put(db, 'runtime', 'journal_sequence', sequence);put(db, 'runtime', 'journal_commit', commit)
        check_guards(root, guards);crash('before_commit');db.execute('COMMIT')
        return {'sequence': sequence, 'commit': commit, 'frontier_sha256': new_frontier,
          'state': state, 'mathematical_node_soundness_checked': False}
    except BaseException:
        try:
            db.execute('ROLLBACK')
        except sqlite3.Error:
            pass
        raise
    finally:
        db.close()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source', type=Path);ap.add_argument('--database', type=Path, required=True)
    ap.add_argument('--root', type=Path, default=Path(__file__).parents[1])
    ap.add_argument('--expected-sha256');ap.add_argument('--receipt', type=Path, required=True)
    args = ap.parse_args();assert not args.receipt.exists()
    result = import_snapshot(args.source, args.database, args.root,
                             expected_source_sha256=args.expected_sha256)
    args.receipt.write_text(json.dumps(result, indent=2)+'\n', encoding='utf8')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
