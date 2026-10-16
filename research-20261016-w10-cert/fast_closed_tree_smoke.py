"""Create a comparable fast-interpreter copy of the proved real subtree.

No search or input data are changed.  The comparison uses precisely the
previously checked 63 nodes and 32 compact leaf payloads.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
old = ROOT / 'StructuralW10Cert20261016/ClosedTreeSmoke.lean'
new = ROOT / 'StructuralW10Cert20261016/FastClosedTreeSmoke.lean'
source = old.read_text(encoding='utf8')
source = source.replace('import StructuralW10Cert20261016.LeafDispatch',
                        'import StructuralW10Cert20261016.FastPruefer')
source = source.replace('StructuralW10Cert20261016.ClosedTreeSmoke',
                        'StructuralW10Cert20261016.FastClosedTreeSmoke')
source = source.replace('def leafCheck := LeafDispatch.check payload',
                        'def leafCheck := FastPruefer.dispatch payload')
source = source.replace('(LeafDispatch.check_sound payload)',
                        '(FastPruefer.dispatch_sound payload)')
new.write_text(source, encoding='utf8', newline='\n')
record = {
    'scope': 'Same real closed subtree; only the executable leaf interpreter changes.',
    'nodes': 63, 'numeric_leaves': 32,
    'baseline_source': str(old.relative_to(ROOT)),
    'baseline_sha256': hashlib.sha256(old.read_bytes()).hexdigest(),
    'source': str(new.relative_to(ROOT)),
    'source_sha256': hashlib.sha256(new.read_bytes()).hexdigest(),
}
(HERE / 'fast-closed-tree-smoke-generated.json').write_text(
    json.dumps(record, indent=2) + '\n', encoding='utf8')
print(json.dumps(record), flush=True)
