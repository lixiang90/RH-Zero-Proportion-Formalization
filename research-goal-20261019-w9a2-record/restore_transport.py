"""Reconstruct only explicitly pinned large evidence, checking every byte."""
from pathlib import Path
from hashlib import sha256
import gzip
import json

ROOT = Path(__file__).resolve().parent.parent
manifest = json.loads((Path(__file__).resolve().parent / 'checkpoint-files.json').read_bytes())
for item in manifest['transported_originals']:
    chunks = []
    for rel in item['parts']:
        data = (ROOT / rel).read_bytes()
        assert len(data) == manifest['files'][rel]['bytes']
        assert sha256(data).hexdigest() == manifest['files'][rel]['sha256']
        chunks.append(data)
    zipped = b''.join(chunks)
    assert len(zipped) == item['gzip_bytes'] and sha256(zipped).hexdigest() == item['gzip_sha256']
    data = gzip.decompress(zipped)
    assert len(data) == item['bytes'] and sha256(data).hexdigest() == item['sha256']
    target = (ROOT / item['path']).resolve()
    assert target.is_relative_to(ROOT.resolve())
    if target.exists():
        assert target.read_bytes() == data, 'refusing to overwrite differing evidence'
    else:
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as stream:
            stream.write(data)
    print(item['path'], item['sha256'])
