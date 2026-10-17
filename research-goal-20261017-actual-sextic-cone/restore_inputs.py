"""Verify lossless input pieces; optionally restore an absent original.

Default is read-only. --restore creates absent originals only, after all
piece and concatenation hashes pass; existing originals are never replaced.
No NumPy, solver, coefficient generation, or numerical transformation.
"""
from pathlib import Path
import argparse,hashlib,json
HERE=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--restore',action='store_true');args=ap.parse_args()
doc=json.loads((HERE/'restore-inputs.json').read_bytes());restored=0
for row in doc['outputs']:
    target=HERE/row['name'];assert target.resolve().parent==HERE.resolve();parts=[]
    for item in row['parts']:
        p=HERE/item['name'];assert p.resolve().parent==HERE.resolve();b=p.read_bytes()
        assert len(b)==item['bytes'] and hashlib.sha256(b).hexdigest()==item['sha256'];parts.append(b)
    raw=b''.join(parts)
    assert len(raw)==row['bytes'] and hashlib.sha256(raw).hexdigest()==row['sha256']
    if target.exists():assert target.read_bytes()==raw
    elif args.restore:
        with target.open('xb') as stream:stream.write(raw)
        restored+=1
print(json.dumps({'outputs_verified':len(doc['outputs']),'absent_originals_restored':restored,'existing_originals_overwritten':0}))
