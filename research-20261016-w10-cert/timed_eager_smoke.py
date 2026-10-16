"""Prepare the same timed subtree with forced dual and move numerals."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
old = ROOT / 'StructuralW10Cert20261016/TimedForce2Smoke.lean'
new = ROOT / 'StructuralW10Cert20261016/TimedEagerLeafSmoke.lean'
source = old.read_text(encoding='utf8')
source = source.replace('import StructuralW10Cert20261016.FastPruefer',
                        'import StructuralW10Cert20261016.EagerLeaf')
source = source.replace('StructuralW10Cert20261016.TimedForce2Smoke',
                        'StructuralW10Cert20261016.TimedEagerLeafSmoke')
source = source.replace('ForcedCoverage2.dispatch', 'EagerLeaf.dispatch')
new.write_text(source, encoding='utf8', newline='\n')
record = {'scope': 'Source preparation only, same 63-node closed subtree.',
          'baseline_sha256': hashlib.sha256(old.read_bytes()).hexdigest(),
          'source_sha256': hashlib.sha256(new.read_bytes()).hexdigest(),
          'source': str(new.relative_to(ROOT))}
(HERE / 'timed-eager-smoke-generated.json').write_text(
    json.dumps(record, indent=2) + '\n', encoding='utf8')
print(json.dumps(record), flush=True)
