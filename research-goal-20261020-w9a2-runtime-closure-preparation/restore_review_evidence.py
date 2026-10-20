"""Restore exact large audit JSON from deterministic gzip transport, no overwrite."""
import gzip
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent


def digest(blob):return hashlib.sha256(blob).hexdigest()


def main():
    manifest=json.loads((HERE/'transport-files.json').read_text())
    for row in manifest['entries']:
        compressed=(HERE/row['transport']).resolve();target=(HERE/row['raw_path']).resolve()
        if not compressed.is_relative_to(HERE) or not target.is_relative_to(HERE):
            raise RuntimeError('Transport path escapes evidence folder')
        packed=compressed.read_bytes()
        if digest(packed)!=row['transport_sha256']:raise RuntimeError('Transport SHA mismatch')
        data=gzip.decompress(packed)
        if digest(data)!=row['raw_sha256'] or len(data)!=row['raw_bytes']:
            raise RuntimeError('Reconstructed raw SHA/byte count mismatch')
        if target.exists():
            if target.read_bytes()!=data:raise RuntimeError('Existing raw evidence differs; refusing overwrite')
        else:
            target.parent.mkdir(parents=True,exist_ok=True)
            with target.open('xb') as stream:stream.write(data)
    print('Exact audit evidence present; no compiler/export/kernel action')


if __name__=='__main__':main()
