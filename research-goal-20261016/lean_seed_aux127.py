"""Extract only the authorized 127-leaf data from hash-bound frozen inputs.

The resulting seed is untrusted mathematical data: Lean independently
checks its complete selected subtree and every materialized geometry step.
"""
from pathlib import Path
import gzip
import hashlib
import json
import re

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
OLD=ROOT/'research-20261016-w10-cert'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
tree_raw=(OLD/'ordered-proof-input.json').read_bytes()
compact_raw=(OLD/'ordered-compact.json').read_bytes()
source=(ROOT/'StructuralGoal20261016/LeanCoverPart001.lean').read_bytes()
assert sha(tree_raw)=='6f2bc79db4613b4130659c9e65e0a24ee07cc50fb0686878d01a8e3f73839c3e'
assert sha(compact_raw)=='5fbb16de9f2b74d1816d7e251efb16c07c4f318a1aedf1a390f18ef6fe499463'
assert sha(source)=='d9d834f81cb334fca36dc5794f0560c611acb2ea139ce7289b933d336ecad271'
tree=json.loads(tree_raw);compact=json.loads(compact_raw);prefix='r0010'
ancestor={prefix[:n]for n in range(1,len(prefix))}
branches=[{k:r[k] for k in ['path','axis','cut']}for r in tree['branches']
          if r['path'].startswith(prefix)or r['path']in ancestor]
leaves=[{k:r[k]for k in ['path','kind','support_hex','tree_code']}for r in compact['leaves']
        if r['path'].startswith(prefix)]
assert len(branches)==130 and len(leaves)==127 and all(r['kind']=='numeric'for r in leaves)
literal=re.search(r'def initialCell : Cl := (.+)\n',source.decode('utf8')).group(1)
packet={'scope':__doc__,'prefix':prefix,'root':tree['root'],'branches':branches,'leaves':leaves,
        'selected_cell_literal':literal,'provenance_tree_sha256':sha(tree_raw),
        'provenance_compact_sha256':sha(compact_raw),'provenance_old_source_sha256':sha(source),
        'mathematical_data_trusted':False,'complete_W10_cover':False}
raw=json.dumps(packet,sort_keys=True,separators=(',',':')).encode('utf8')
packed=gzip.compress(raw,compresslevel=9,mtime=0)
p=HERE/'lean_aux127_seed.json.gz'
if p.exists():
    assert p.read_bytes()==packed, 'Preserve the frozen seed'
else:
    p.write_bytes(packed)
print(json.dumps({'seed_sha256':sha(packed),'seed_bytes':len(packed),'uncompressed_bytes':len(raw)}))
