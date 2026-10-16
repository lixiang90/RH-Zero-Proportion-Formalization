"""Independent bounded baseline roundtrip audit; stdlib and readonly SQLite.

Uses its own incremental source decoder and serialization implementation,
without importing the store producer or mathematical discovery modules.
Checks every canonical unit, key/order/hash, all small metadata and original
frontier; checks total raw-source and whole canonical-document hashes. This
is storage fidelity, not mathematical validation of the contained witnesses.
"""
from pathlib import Path
import argparse, codecs, ctypes, hashlib, json, os, sqlite3, time


def encode(value):
    return json.dumps(value, ensure_ascii=True, sort_keys=True, allow_nan=False,
                      separators=(',', ':')).encode('ascii')


def source_file(path):
    if os.name != 'nt':
        return Path(path).open('rb')
    import msvcrt
    from ctypes import wintypes
    kernel = ctypes.WinDLL('kernel32', use_last_error=True)
    kernel.CreateFileW.argtypes = [wintypes.LPCWSTR, wintypes.DWORD, wintypes.DWORD,
      wintypes.LPVOID, wintypes.DWORD, wintypes.DWORD, wintypes.HANDLE]
    kernel.CreateFileW.restype = wintypes.HANDLE
    handle = kernel.CreateFileW(str(Path(path).resolve()), 0x80000000, 1|2|4, None, 3, 0x08000000, None)
    if handle == wintypes.HANDLE(-1).value:
        raise ctypes.WinError(ctypes.get_last_error())
    return os.fdopen(msvcrt.open_osfhandle(handle, os.O_RDONLY|os.O_BINARY), 'rb')


class Decoder:
    def __init__(self, path):
        self.file = source_file(path);self.text = '';self.done = False
        self.utf8 = codecs.getincrementaldecoder('utf-8')();self.decoder = json.JSONDecoder()
        self.hash = hashlib.sha256();self.bytes = 0;self.maximum_buffer_chars = 0
    def fill(self):
        raw = self.file.read(256<<10);self.hash.update(raw);self.bytes += len(raw)
        if not raw:
            self.done = True
        self.text += self.utf8.decode(raw, final=self.done)
        self.maximum_buffer_chars = max(self.maximum_buffer_chars, len(self.text))
    def peek(self):
        self.text = self.text.lstrip()
        while not self.text and not self.done:
            self.fill();self.text = self.text.lstrip()
        return self.text[:1]
    def token(self, char):
        assert self.peek() == char
        self.text = self.text[1:]
    def value(self):
        self.peek()
        while True:
            try:
                value, end = self.decoder.raw_decode(self.text)
                if end == len(self.text) and not self.done:
                    self.fill();continue
                self.text = self.text[end:];return value
            except json.JSONDecodeError:
                if self.done:
                    raise
                self.fill()


def control(db, name):
    row = db.execute('SELECT payload FROM control WHERE name=?', (name,)).fetchone();assert row
    return json.loads(row[0])


def database_document_hash(db, section_counts):
    h = hashlib.sha256();h.update(b'{');first = True
    for position, name, kind in db.execute('SELECT position,name,kind FROM fields ORDER BY position'):
        if not first:
            h.update(b',')
        first = False;h.update(encode(name)+b':')
        if kind == 'metadata':
            payload, wanted = db.execute('SELECT payload,digest FROM metadata WHERE name=?', (name,)).fetchone()
            assert hashlib.sha256(payload).hexdigest() == wanted;h.update(payload)
        else:
            mapping = kind == 'map';h.update(b'{' if mapping else b'[');seen = 0
            query = 'SELECT position,item_key,payload,digest FROM entries WHERE section=? AND position<? ORDER BY position'
            for n, key, payload, wanted in db.execute(query, (name, section_counts[name])):
                assert n == seen and hashlib.sha256(payload).hexdigest() == wanted
                if seen:
                    h.update(b',')
                if mapping:
                    h.update(encode(key)+b':')
                h.update(payload);seen += 1
            assert seen == section_counts[name];h.update(b'}' if mapping else b']')
    h.update(b'}');return h.hexdigest()


def replay(source, database, root):
    started = time.monotonic();db = sqlite3.connect(Path(database).resolve().as_uri()+'?mode=ro', uri=True)
    db.execute('PRAGMA cache_size=-8192');db.execute('PRAGMA mmap_size=0');db.execute('PRAGMA temp_store=FILE')
    assert control(db, 'schema') == 'RelevantBelow-KKT-OBBT-SQLite-prototype-v1'
    assert control(db, 'published_after_complete_baseline_commit') is True
    baseline = control(db, 'baseline');source_decoder = Decoder(source)
    fields = iter(db.execute('SELECT position,name,kind FROM fields ORDER BY position'))
    whole = hashlib.sha256();whole.update(b'{');source_decoder.token('{');top = 0
    counts = {};units = 0;largest = 0;guards = None
    while source_decoder.peek() != '}':
        if top:
            whole.update(b',')
        name = source_decoder.value();source_decoder.token(':')
        saved = next(fields);assert saved[0] == top and saved[1] == name
        kind = saved[2];top += 1;whole.update(encode(name)+b':')
        if kind == 'metadata':
            value = source_decoder.value();payload = encode(value)
            stored, digest = db.execute('SELECT payload,digest FROM metadata WHERE name=?', (name,)).fetchone()
            assert payload == stored and hashlib.sha256(payload).hexdigest() == digest
            whole.update(payload)
            if name == 'input_sha256':
                guards = value
        else:
            mapping = kind == 'map';opening, closing = ('{', '}') if mapping else ('[', ']')
            source_decoder.token(opening);whole.update(opening.encode());n = 0
            cursor = iter(db.execute('SELECT position,item_key,payload,digest FROM entries WHERE section=? AND position<? ORDER BY position',
                                     (name, baseline['section_counts'][name])))
            while source_decoder.peek() != closing:
                if n:
                    whole.update(b',')
                if mapping:
                    key = source_decoder.value();source_decoder.token(':');whole.update(encode(key)+b':')
                value = source_decoder.value();payload = encode(value)
                if not mapping:
                    key = str(value[0]) if name == 'tangent_data' else value['path']
                position, stored_key, stored, digest = next(cursor)
                assert position == n and key == stored_key and payload == stored
                assert hashlib.sha256(payload).hexdigest() == digest
                whole.update(payload);n += 1;units += 1;largest = max(largest, len(payload))
                if source_decoder.peek() != ',':
                    break
                source_decoder.token(',')
            source_decoder.token(closing);whole.update(closing.encode());assert next(cursor, None) is None
            assert n == baseline['section_counts'][name];counts[name] = n
        if source_decoder.peek() != ',':
            break
        source_decoder.token(',')
    source_decoder.token('}');whole.update(b'}');assert source_decoder.peek() == ''
    source_decoder.file.close();assert next(fields, None) is None
    assert source_decoder.hash.hexdigest() == baseline['source_sha256']
    assert source_decoder.bytes == baseline['source_bytes']
    assert whole.hexdigest() == baseline['canonical_document_sha256']
    assert database_document_hash(db, counts) == whole.hexdigest()
    assert guards is not None
    for name, digest in guards.items():
        path = Path(root)/Path(name.replace('\\', '/'))
        assert hashlib.sha256(path.read_bytes()).hexdigest() == digest
    assert db.execute('PRAGMA integrity_check').fetchone()[0] == 'ok'
    journal_nodes = db.execute('SELECT count(*) FROM node_log').fetchone()[0]
    db.close()
    return {'scope': __doc__, 'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'source_snapshot_sha256': source_decoder.hash.hexdigest(), 'source_snapshot_bytes': source_decoder.bytes,
      'canonical_document_sha256': whole.hexdigest(), 'canonical_units_independently_compared': units,
      'section_counts': counts, 'largest_unit_bytes': largest,
      'independent_decoder_maximum_buffer_chars': source_decoder.maximum_buffer_chars,
      'all_entry_payloads_orders_and_hashes_matched': True, 'all_metadata_and_baseline_frontier_matched': True,
      'SQLite_integrity_check': 'ok', 'all_frozen_source_hashes_matched': True,
      'post_baseline_node_transactions_present': journal_nodes,
      'post_baseline_transactions_semantically_replayed_here': False,
      'baseline_semantic_witness_replay': False, 'entire_history_loaded_in_memory': False,
      'new_search_started': False, 'new_zero_proportion_proven': False,
      'seconds': time.monotonic()-started}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source', type=Path);ap.add_argument('--database', type=Path, required=True)
    ap.add_argument('--root', type=Path, default=Path(__file__).parents[1]);ap.add_argument('--receipt', type=Path, required=True)
    args = ap.parse_args();assert not args.receipt.exists()
    result = replay(args.source, args.database, args.root)
    args.receipt.write_text(json.dumps(result, indent=2)+'\n', encoding='utf8')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
