"""Restore absent archive inputs and hash-identical derived semantic caches.

Existing files must already have their exact pinned contents; they are never
overwritten. No optimizer, Lean compiler, or certificate search is invoked.
"""
from pathlib import Path
import gzip, hashlib, json, struct

HERE=Path(__file__).resolve().parent
AUDIT=HERE.with_name('w10-size-audit-20261017')
sha=lambda raw:hashlib.sha256(raw).hexdigest()

def restore(path,raw,expected):
    assert sha(raw)==expected['sha256'] and len(raw)==expected['bytes'],path
    if path.exists():assert path.read_bytes()==raw,path
    else:path.write_bytes(raw)

manifest=json.loads((HERE/'restore-inputs.json').read_bytes())
for row in manifest['outputs']:
    target=HERE/row['name'];assert target.resolve().parent==HERE.resolve()
    pieces=[]
    for r in row['parts']:
        p=HERE/r['name'];assert p.resolve().parent==HERE.resolve()
        b=p.read_bytes();assert sha(b)==r['sha256'] and len(b)==r['bytes'];pieces.append(b)
    raw=b''.join(pieces)
    if row['encoding']=='gzip':raw=gzip.decompress(raw)
    else:assert row['encoding']=='concatenation'
    restore(target,raw,row)

# This is a zero-merge packet. Its complete retained semantics recreate the
# old caches exactly; comparison to the independently pinned old cache hashes
# is mandatory. They are outputs, not additional trusted mathematical input.
packet=json.loads(gzip.decompress((HERE/'merged-tree.json.gz').read_bytes()))
assert packet['successful_parent_checks']==0
branches={r['path']:r for r in packet['branches']};leaves={r['path']:r for r in packet['leaves']}
assert len(branches)==95778 and len(leaves)==95779
nodes=bytearray();fs=bytearray();codes=bytearray();stack=['r']
while stack:
    path=stack.pop()
    if path in branches:
        r=branches[path];nodes.extend(struct.pack('<BBI',1,r['axis'],r['cut']))
        stack.extend([path+'1',path+'0'])
    else:
        r=leaves[path]
        if r['kind']=='numeric':
            assert r['original_witness_path']==path and len(r['FS'])==39
            nodes.append(0);codes.extend(struct.pack('<I',r['tree_code']))
            for k,m,p,q in r['FS']:
                assert p%32==q%32==0
                fs.extend(struct.pack('<BHHH',k,m,p//32,q//32))
        elif r['kind']=='empty':nodes.extend(bytes([2,r['violation_axis']]))
        else:assert r['kind']=='reflection';nodes.append(3)
expected={r['path']:r for r in json.loads((AUDIT/'semantics.json').read_bytes())['cache_files']}
for name,raw in [('nodes.bin',nodes),('fs.bin',fs),('treecodes.bin',codes)]:
    restore(AUDIT/name,bytes(raw),expected[name])
print(json.dumps({'restored_or_exact_existing':len(manifest['outputs']),
                  'derived_old_semantic_cache_hashes_verified':3,'existing_files_overwritten':0}))
