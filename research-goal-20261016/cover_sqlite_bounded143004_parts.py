"""Lossless <=4MiB pieces for the bounded epoch's standalone gzip.

The manifest binds each piece and the exact concatenated gzip. Replay
assembles a verified temporary compressed file with bounded memory and
then calls the independent streaming mathematical verifier.
"""
from pathlib import Path
import argparse, hashlib, json, tempfile

LIMIT = 4*(1<<20)


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda: f.read(1<<20), b''):
            h.update(b)
    return h.hexdigest()


def split(archive, manifest):
    assert not manifest.exists()
    pieces = [];whole = hashlib.sha256();total = 0
    with archive.open('rb') as source:
        while True:
            b = source.read(LIMIT)
            if not b:
                break
            p = archive.with_name(archive.name+f'.part{len(pieces):03d}')
            with p.open('xb') as f:
                f.write(b)
            whole.update(b);total += len(b)
            pieces.append({'name': p.name, 'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()})
    r = {'schema': 'exact-gzip-byte-pieces-v1', 'piece_limit': LIMIT,
      'gzip_bytes': total, 'gzip_sha256': whole.hexdigest(), 'pieces': pieces}
    assert total == archive.stat().st_size and r['gzip_sha256'] == digest(archive)
    manifest.write_text(json.dumps(r, indent=2)+'\n', encoding='utf8')
    # Independently re-read every piece and bind the reconstructed byte stream.
    verify(manifest)
    return r


def verify(manifest, target=None):
    r = json.loads(manifest.read_bytes());assert r['schema'] == 'exact-gzip-byte-pieces-v1'
    assert r['piece_limit'] == LIMIT and r['pieces']
    h = hashlib.sha256();total = 0
    for i, row in enumerate(r['pieces']):
        assert Path(row['name']).name == row['name']
        p = manifest.parent/row['name'];part = hashlib.sha256();n = 0
        with p.open('rb') as f:
            for b in iter(lambda: f.read(1<<20), b''):
                part.update(b);h.update(b);n += len(b)
                if target is not None:
                    target.write(b)
        assert n == row['bytes'] and 0 < n <= LIMIT and part.hexdigest() == row['sha256']
        assert i == len(r['pieces'])-1 or n == LIMIT
        total += n
    assert total == r['gzip_bytes'] and h.hexdigest() == r['gzip_sha256']
    return r


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--parts', type=Path, required=True)
    ap.add_argument('--receipt', type=Path, required=True)
    ap.add_argument('--node-log', type=Path, required=True)
    args = ap.parse_args();assert not args.receipt.exists() and not args.node_log.exists()
    import cover_sqlite_bounded143004_archive as independent
    with tempfile.TemporaryDirectory(prefix='verified-gzip-', dir=args.receipt.resolve().parent) as tmp:
        archive = Path(tmp)/'standalone.jsonl.gz'
        with archive.open('xb') as target:
            r = verify(args.parts, target)
        assert digest(archive) == r['gzip_sha256']
        result = independent.replay(archive, args.receipt, args.node_log)
    print(json.dumps({'passed': result['passed'], 'nodes': result['journal_nodes'],
      'gzip_sha256': r['gzip_sha256']}), flush=True)


if __name__ == '__main__':
    main()
