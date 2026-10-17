"""Make lossless 3MiB pieces of the already independently audited NPZ.

This does not recompute or alter any numeric coefficient. Existing pieces
and manifest must match exactly. The raw NPZ is a reconstructed dependency,
not a second repository upload.
"""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
SOURCE=HERE/'new-rows-float.npz';OUT=HERE/'restore-inputs.json'
raw=SOURCE.read_bytes()
assert len(raw)==6980634 and hashlib.sha256(raw).hexdigest()=='213be8da6f73755e582763ef63ea2685041aed5d1af6b98f44a0116672f4009c'
parts=[]
for k,start in enumerate(range(0,len(raw),3*1024**2)):
    p=HERE/(SOURCE.name+f'.part{k:03d}');b=raw[start:start+3*1024**2]
    if p.exists():assert p.read_bytes()==b
    else:p.write_bytes(b)
    parts.append({'name':p.name,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
doc={'scope':__doc__,'outputs':[{'name':SOURCE.name,'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),'parts':parts}]}
encoded=(json.dumps(doc,indent=2,allow_nan=False)+'\n').encode()
if OUT.exists():assert OUT.read_bytes()==encoded
else:OUT.write_bytes(encoded)
assert b''.join((HERE/r['name']).read_bytes() for r in parts)==raw
print(json.dumps({'parts':len(parts),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),'uncompressed_NPZ_not_to_be_staged':True}))
