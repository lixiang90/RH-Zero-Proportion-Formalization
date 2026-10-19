"""Pin the completed analysis and transport large evidence losslessly.

The original numerical files and producer manifests are never modified.
Large originals are represented in Git by deterministic gzip chunks and can
be restored by restore_transport.py. This is not a proof-verification runner.
"""
from pathlib import Path
from hashlib import sha256
import gzip
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
LIMIT = 2_000_000
CHUNK = 1_200_000

def digest(data):
    return sha256(data).hexdigest()

def main():
    out = HERE / 'checkpoint-files.json'
    assert not out.exists(), 'frozen checkpoint already exists'
    folders = sorted(p for p in ROOT.iterdir() if p.is_dir() and p.name.startswith('research-goal-20261019-w9a2-'))
    original_paths = sorted(p for folder in folders for p in folder.rglob('*') if p.is_file() and '__pycache__' not in p.parts)
    files = {}
    transported = []
    for path in original_paths:
        data = path.read_bytes()
        rel = path.relative_to(ROOT).as_posix()
        if len(data) <= LIMIT:
            files[rel] = {'bytes': len(data), 'sha256': digest(data)}
            continue
        zipped = gzip.compress(data, compresslevel=9, mtime=0)
        parts = []
        for i, offset in enumerate(range(0, len(zipped), CHUNK)):
            part = HERE / 'transport' / (path.parent.name + '--' + path.name + f'.gzip.part{i:03d}')
            part.parent.mkdir(exist_ok=True)
            with part.open('xb') as stream:
                stream.write(zipped[offset:offset + CHUNK])
            raw = part.read_bytes()
            relpart = part.relative_to(ROOT).as_posix()
            files[relpart] = {'bytes': len(raw), 'sha256': digest(raw)}
            parts.append(relpart)
        transported.append({'path': rel, 'bytes': len(data), 'sha256': digest(data), 'gzip_bytes': len(zipped), 'gzip_sha256': digest(zipped), 'parts': parts})
    extra = ['research-goal-20261016/direction-state.json', 'research-goal-20261016/DIRECTION.zh.md', 'research-goal-20261016/macro-reviews/007-20261019.zh.md']
    for rel in extra:
        data = (ROOT / rel).read_bytes()
        files[rel] = {'bytes': len(data), 'sha256': digest(data)}
    payload = {'scope': 'Analysis evidence and unformalized candidates; not a newly kernel-verified zero proportion.', 'files': files, 'transported_originals': transported, 'restore': 'C:/Python314/python.exe -B -X utf8 research-goal-20261019-w9a2-record/restore_transport.py'}
    out.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
    print(json.dumps({'files': len(files), 'bytes': sum(x['bytes'] for x in files.values()), 'transported_originals': [{k: x[k] for k in ['path','bytes','gzip_bytes']} for x in transported], 'manifest_sha256': digest(out.read_bytes())}, indent=2))

if __name__ == '__main__':
    main()
