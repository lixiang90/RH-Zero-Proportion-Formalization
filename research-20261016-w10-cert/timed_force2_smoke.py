"""Prepare a comparable timed experiment forcing read, next cursor and payload."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
old = ROOT / 'StructuralW10Cert20261016/TimedClosedTreeSmoke.lean'
new = ROOT / 'StructuralW10Cert20261016/TimedForce2Smoke.lean'
source = old.read_text(encoding='utf8')
source = source.replace('import StructuralW10Cert20261016.ForcedCoverage',
                        'import StructuralW10Cert20261016.ForcedCoverage2')
source = source.replace('StructuralW10Cert20261016.TimedClosedTreeSmoke',
                        'StructuralW10Cert20261016.TimedForce2Smoke')
source = source.replace('ForcedCoverage.walk', 'ForcedCoverage2.walk')
source = source.replace('FastPruefer.dispatch', 'ForcedCoverage2.dispatch')
new.write_text(source, encoding='utf8', newline='\n')
record = {'scope': 'Source preparation only, same 63-node closed subtree.',
          'baseline_sha256': hashlib.sha256(old.read_bytes()).hexdigest(),
          'source_sha256': hashlib.sha256(new.read_bytes()).hexdigest(),
          'source': str(new.relative_to(ROOT))}
(HERE / 'timed-force2-smoke-generated.json').write_text(
    json.dumps(record, indent=2) + '\n', encoding='utf8')
print(json.dumps(record), flush=True)
