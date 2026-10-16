"""Prepare a timing-only walk whose leaves return true.

No coverage theorem is asserted: this isolates the forced geometry work from
the numerical leaf checker, using the same actual split tree.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
old = ROOT / 'StructuralW10Cert20261016/TimedForce2Smoke.lean'
new = ROOT / 'StructuralW10Cert20261016/CellOnlySmoke.lean'
source = old.read_text(encoding='utf8')
source = source.replace('StructuralW10Cert20261016.TimedForce2Smoke',
                        'StructuralW10Cert20261016.CellOnlySmoke')
source = source.replace('def leafCheck := ForcedCoverage2.dispatch payload',
                        'def leafCheck (_c : Cl) (_id : ℕ) : Bool := true')
source = source.split('\ntheorem covered :', 1)[0]
source += '\nend StructuralW10Cert20261016.CellOnlySmoke\nend\n'
new.write_text(source, encoding='utf8', newline='\n')
record = {'scope': 'Timing experiment only: all leaf checks are true, so no floor or coverage is proved.',
          'nodes': 63, 'numeric_leaves': 32,
          'source_sha256': hashlib.sha256(new.read_bytes()).hexdigest(),
          'source': str(new.relative_to(ROOT))}
(HERE / 'cell-only-smoke-generated.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf8')
print(json.dumps(record), flush=True)
