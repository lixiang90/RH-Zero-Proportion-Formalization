"""Extract only the authorized r0011 data from the frozen old W10 tree.

The self-contained seed is untrusted mathematical data. Lean independently
checks every materialized state, numerical leaf, and coverage composition.
"""
from pathlib import Path
import collections
import gzip
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OLD = ROOT / 'research-20261016-w10-cert'
sha = lambda raw: hashlib.sha256(raw).hexdigest()
tree_raw = (OLD / 'ordered-proof-input.json').read_bytes()
compact_raw = (OLD / 'ordered-compact.json').read_bytes()
assert sha(tree_raw) == '6f2bc79db4613b4130659c9e65e0a24ee07cc50fb0686878d01a8e3f73839c3e'
assert sha(compact_raw) == '5fbb16de9f2b74d1816d7e251efb16c07c4f318a1aedf1a390f18ef6fe499463'
tree = json.loads(tree_raw)
compact = json.loads(compact_raw)
prefix = 'r0011'
ancestors = {prefix[:n] for n in range(1, len(prefix))}
branches = [{k: r[k] for k in ('path', 'axis', 'cut')} for r in tree['branches']
            if r['path'].startswith(prefix) or r['path'] in ancestors]
leaves = [{k: r[k] for k in ('path', 'kind', 'support_hex', 'tree_code')}
          for r in compact['leaves'] if r['path'].startswith(prefix)]
types = dict(collections.Counter(r['kind'] for r in leaves))
assert len(branches) == 481 and len(leaves) == 478 and types == {'numeric': 478}
packet = {'scope': __doc__, 'prefix': prefix, 'root': tree['root'],
          'branches': branches, 'leaves': leaves,
          'provenance_tree_sha256': sha(tree_raw),
          'provenance_compact_sha256': sha(compact_raw),
          'leaf_types': types, 'mathematical_data_trusted': False,
          'complete_W10_cover': False}
raw = json.dumps(packet, sort_keys=True, separators=(',', ':')).encode('utf8')
packed = gzip.compress(raw, compresslevel=9, mtime=0)
p = HERE / 'lean_aux478_seed.json.gz'
if p.exists():
    assert p.read_bytes() == packed, 'Preserve the existing seed'
else:
    p.write_bytes(packed)
print(json.dumps({'seed_sha256': sha(packed), 'seed_bytes': len(packed),
                  'uncompressed_bytes': len(raw), 'leaf_types': types,
                  'subtree_branches': 477, 'ancestor_branches': 4}))
