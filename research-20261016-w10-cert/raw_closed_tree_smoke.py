"""Prepare ordinary FS/move literals for precisely the same 63-node subtree."""
from pathlib import Path
import hashlib
import json
import re
import emit_tree as emit
import ordered_generate as og
import relative_codec as codec

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
old = ROOT / 'StructuralW10Cert20261016/TimedForce2Smoke.lean'
new = ROOT / 'StructuralW10Cert20261016/RawClosedTreeSmoke.lean'
source = old.read_text(encoding='utf8')
prefix = re.search(r'-- original subtree (r[01]+)', source).group(1)
doc = json.loads((HERE / 'ordered-0.json').read_bytes())
records = sorted((a for a in doc['accepted'] if a['path'].startswith(prefix)), key=lambda a: a['path'])
assert len(records) == 32
source = source.replace('StructuralW10Cert20261016.TimedForce2Smoke',
                        'StructuralW10Cert20261016.RawClosedTreeSmoke')
source = source.replace('import StructuralW10Cert20261016.FastPruefer',
                        'import StructuralW10Cert20261016.RawLeaf')
head, tail = source.split('def D0 :', 1)
tail = tail.split('def leafCheck :=', 1)[1]
names = []
declarations = []
fmt = lambda xs: '[' + ', '.join('(' + ', '.join(map(str, x)) + ')' for x in xs) + ']'
for i, rec in enumerate(records):
    result = rec['result']
    prepared = codec.prepare(result, 4)
    lo = result['certificate']['lower_bounds']
    hi = result['certificate']['upper_bounds']
    # tree_flow stores its direct moves in [i,j,isUpper,Y] form.
    fs = prepared['FS']
    reconstruction = codec.tree.recompute(fs, lo, hi)
    assert reconstruction['tree_code'] == prepared['tree_code']
    dual = []
    for a, b, upper, y in reconstruction['steps']:
        slot = a * (17-a) // 2 + b-a-2
        dual.append((slot, 0 if upper else int(y), int(y) if upper else 0))
    name = 'C' + str(i)
    names.append(name)
    declarations.append(f'def {name} : RawLeaf.Certificate := ({fmt(fs)}, {fmt(dual)})\n')
declarations.append('def raw (n : ℕ) : RawLeaf.Certificate := ' + emit.balanced(names) + '\n')
source = head + ''.join(declarations) + 'def leafCheck := RawLeaf.dispatch raw' + tail.split(' payload', 1)[1]
source = source.replace('(ForcedCoverage2.dispatch_sound payload)', '(RawLeaf.dispatch_sound raw)')
new.write_text(source, encoding='utf8', newline='\n')
record = {'scope': 'Same real closed subtree, raw ordinary FS/move literals; proof replay remains required.',
          'nodes': 63, 'numeric_leaves': 32, 'source_bytes': len(new.read_bytes()),
          'source_sha256': hashlib.sha256(new.read_bytes()).hexdigest(), 'lean_passed': False}
(HERE / 'raw-closed-tree-smoke-generated.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf8')
print(json.dumps(record), flush=True)
