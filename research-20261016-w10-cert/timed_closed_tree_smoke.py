"""Instrument the proved subtree to measure certificate work after imports.

The timing command is used only in this experiment, not in the submission.
The theorem and the certificate inputs are copied without changes.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
old = ROOT / 'StructuralW10Cert20261016/ForcedClosedTreeSmoke.lean'
new = ROOT / 'StructuralW10Cert20261016/TimedClosedTreeSmoke.lean'
source = old.read_text(encoding='utf8')
source = source.replace('StructuralW10Cert20261016.ForcedClosedTreeSmoke',
                        'StructuralW10Cert20261016.TimedClosedTreeSmoke')
timer = '''
elab "#w10_timing" label:str : command => do
  let tick ← IO.monoMsNow
  Lean.logInfo m!"W10_TIMING {label.getString} {tick}"
'''
source = source.replace('noncomputable section\n', timer + '\nnoncomputable section\n', 1)
source = source.replace('noncomputable section\n', 'set_option Elab.async false\nnoncomputable section\n', 1)
source = source.replace('theorem checked :', '#w10_timing "certificate_begin"\ntheorem checked :', 1)
source = source.replace('\ntheorem covered :', '\n#w10_timing "certificate_end"\n\ntheorem covered :', 1)
source = source.replace('#print axioms covered', '#w10_timing "soundness_end"\n#print axioms covered', 1)
new.write_text(source, encoding='utf8', newline='\n')
record = {'scope': 'Source instrumentation only; pure certificate time excludes imports and data declarations.',
          'baseline_source_sha256': hashlib.sha256(old.read_bytes()).hexdigest(),
          'source_sha256': hashlib.sha256(new.read_bytes()).hexdigest(),
          'source': str(new.relative_to(ROOT)), 'nodes': 63, 'numeric_leaves': 32}
(HERE / 'timed-closed-tree-smoke-generated.json').write_text(
    json.dumps(record, indent=2) + '\n', encoding='utf8')
print(json.dumps(record), flush=True)
