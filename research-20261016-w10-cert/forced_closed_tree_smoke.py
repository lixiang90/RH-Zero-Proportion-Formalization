"""Create the same real subtree with forced cells and the fast flow interpreter."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
old = ROOT / 'StructuralW10Cert20261016/FastClosedTreeSmoke.lean'
new = ROOT / 'StructuralW10Cert20261016/ForcedClosedTreeSmoke.lean'
source = old.read_text(encoding='utf8')
source = source.replace('import StructuralW10Cert20261016.OrderCoverage',
                        'import StructuralW10Cert20261016.ForcedCoverage')
source = source.replace('StructuralW10Cert20261016.FastClosedTreeSmoke',
                        'StructuralW10Cert20261016.ForcedClosedTreeSmoke')
source = source.replace('OrderCoverage.walk', 'ForcedCoverage.walk')
new.write_text(source, encoding='utf8', newline='\n')
record = {'scope': 'Same real 63-node subtree with forced cell arithmetic.',
          'nodes': 63, 'numeric_leaves': 32,
          'baseline_sha256': hashlib.sha256(old.read_bytes()).hexdigest(),
          'source_sha256': hashlib.sha256(new.read_bytes()).hexdigest()}
(HERE / 'forced-closed-tree-smoke-generated.json').write_text(
    json.dumps(record, indent=2) + '\n', encoding='utf8')
print(json.dumps(record), flush=True)
