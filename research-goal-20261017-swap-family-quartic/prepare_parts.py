"""Prepare lossless <=3MiB pieces of the two frozen research packets."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;OUT=HERE/'restore-inputs.json';SIZE=3*1024*1024
assert not OUT.exists();rows=[]
for name in ['swap-family-quartic.json.gz','swap-family-normalized.json.gz']:
    raw=(HERE/name).read_bytes();parts=[]
    for k,start in enumerate(range(0,len(raw),SIZE)):
        piece=raw[start:start+SIZE];p=HERE/(name+f'.part{k:03d}');assert not p.exists();p.write_bytes(piece)
        parts.append({'name':p.name,'bytes':len(piece),'sha256':hashlib.sha256(piece).hexdigest()})
    rows.append({'name':name,'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),'parts':parts})
OUT.write_text(json.dumps({'scope':__doc__,'maximum_part_bytes':SIZE,'outputs':rows},indent=2)+'\n',encoding='utf8')
print(json.dumps({'outputs':len(rows),'parts':sum(len(r['parts']) for r in rows)}))
