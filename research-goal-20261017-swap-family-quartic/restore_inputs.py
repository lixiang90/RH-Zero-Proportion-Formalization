"""Verify research-packet pieces; optionally restore an absent original.

Existing outputs are always hash-checked and never overwritten. Default
read-only. --restore writes only absent files after complete byte checks.
"""
from pathlib import Path
import argparse,hashlib,json
HERE=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--restore',action='store_true');args=ap.parse_args()
manifest=json.loads((HERE/'restore-inputs.json').read_bytes());count=0
for row in manifest['outputs']:
    target=HERE/row['name'];assert target.resolve().parent==HERE.resolve();chunks=[]
    for r in row['parts']:
        p=HERE/r['name'];assert p.resolve().parent==HERE.resolve();b=p.read_bytes()
        assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256'];chunks.append(b)
    raw=b''.join(chunks);assert len(raw)==row['bytes'] and hashlib.sha256(raw).hexdigest()==row['sha256']
    if target.exists():assert target.read_bytes()==raw
    elif args.restore:target.write_bytes(raw);count+=1
print(json.dumps({'packets_verified':len(manifest['outputs']),'missing_originals_restored':count,'existing_files_overwritten':0}))
