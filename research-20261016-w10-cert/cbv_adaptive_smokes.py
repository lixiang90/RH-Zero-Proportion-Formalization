"""Prepare proof-producing cbv and adaptive normalization comparisons."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
baseline = (ROOT / 'StructuralW10Cert20261016/TimedForce2Smoke.lean').read_text(encoding='utf8')
outputs = []
source = baseline.replace('StructuralW10Cert20261016.TimedForce2Smoke',
                          'StructuralW10Cert20261016.CbvClosedTreeSmoke')
source = 'import Lean.Elab.Tactic.Cbv\n' + source
source = source.replace('  decide +kernel\n#w10_timing "certificate_end"',
                        '  decide_cbv\n#w10_timing "certificate_end"')
outputs.append(('CbvClosedTreeSmoke', source))
source = baseline.replace('StructuralW10Cert20261016.TimedForce2Smoke',
                          'StructuralW10Cert20261016.AdaptiveClosedTreeSmoke')
source = 'import StructuralW10Cert20261016.AdaptiveCoverage\n' + source
source = source.replace('ForcedCoverage2.walk', 'AdaptiveCoverage.walk')
outputs.append(('AdaptiveClosedTreeSmoke', source))
records = []
for name, source in outputs:
    path = ROOT / ('StructuralW10Cert20261016/' + name + '.lean')
    path.write_text(source, encoding='utf8', newline='\n')
    records.append({'module': name, 'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
(HERE / 'cbv-adaptive-smokes-generated.json').write_text(json.dumps(records, indent=2) + '\n', encoding='utf8')
print(json.dumps(records), flush=True)
