"""Freeze the ordinary-kernel dynamic scalar-sector bridge.

This core retains the actual displacement squared. Curvature and point-slope
bounds remain explicit hypotheses; it supplies no new numerical exclusion or
global zero-proportion theorem.
"""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
MODULE = 'StructuralGoal20261016.WindowScalarSector'
EXPECTED = {MODULE + '.' + n for n in
            ('secant_abs', 'square_from_abs', 'actual_square', 'residual_cut')}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


receipt = json.loads((HERE / 'lean_verification.json').read_bytes())
record = {r['module']: r for r in receipt['modules']}[MODULE]
source = MODULE.replace('.', '/') + '.lean'
raw = (ROOT / source).read_bytes()
assert record['passed'] and record['exit_code'] == 0, MODULE
assert record['source_unchanged'] and record['source_sha256'] == digest(raw), MODULE
log = 'research-goal-20261016/' + record['log']
log_bytes = (ROOT / log).read_bytes()
assert digest(log_bytes) == record['log_sha256'], MODULE
printed = log_bytes.decode('utf8', errors='replace')
roots = []
for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", printed):
    listed = [x.strip() for x in axioms.split(',') if x.strip()]
    assert set(listed) <= ALLOWED, (name, listed)
    roots.append({'name': name, 'axioms': listed})
for name in re.findall(r"'([^']+)' does not depend on any axioms", printed):
    roots.append({'name': name, 'axioms': []})
assert len(roots) == 4 and {r['name'] for r in roots} == EXPECTED, roots
assert not re.search(r'\b(sorry|axiom|native_decide)\b', raw.decode('utf8')), source

dependency = 'research-goal-20261016/window_bregman_core_formal_index.json'
dependency_bytes = (ROOT / dependency).read_bytes()
old_index = json.loads(dependency_bytes)
assert old_index['all_current_sources_and_logs_verified']
for r in old_index['records']:
    assert digest((ROOT / r['source']).read_bytes()) == r['source_sha256'], r['source']
    assert digest((ROOT / r['log']).read_bytes()) == r['log_sha256'], r['log']

index = {
    'scope': __doc__,
    'module': MODULE,
    'source': source,
    'source_sha256': digest(raw),
    'source_bytes': len(raw),
    'log': log,
    'log_sha256': digest(log_bytes),
    'olean_sha256': record['olean_sha256'],
    'whole_process_seconds': record['whole_process_seconds'],
    'compiler_sha256': receipt['compiler_sha256'],
    'canonical_receipt': 'research-goal-20261016/lean_verification.json',
    'receipt_record': record,
    'roots': roots,
    'proof_modules': 1,
    'ordinary_Lean_passed': True,
    'all_current_sources_and_logs_verified': True,
    'frozen_dependency_index': dependency,
    'frozen_dependency_index_sha256': digest(dependency_bytes),
    'analytic_hypotheses': [
        'f is the actual WindowKernel.w 24 WindowKernel.d24.',
        'p and x lie in the certified closed interval; m < M.',
        'm <= actual w-second <= M holds throughout that interval.',
        'For actual_square: |actual w-first(p)-S| <= E and tau > 0.',
        'residual_cut requires an upper bound on the actual residual square.'
    ],
    'retains_dynamic_displacement_squared': True,
    'new_actual_local_exclusions': 0,
    'complete_global_cover': False,
    'new_zero_proportion_proven': False,
    'independent_Nanoda_replayed': False,
    'script_sha256': digest(Path(__file__).read_bytes())
}
index_path = HERE / 'window_scalar_sector_formal_index.json'
index_path.write_text(json.dumps(index, indent=2) + '\n', encoding='utf8')
files = ['research-goal-20261016/' + Path(__file__).name,
         source, log, 'research-goal-20261016/' + index_path.name]
sync = {
    'formal_index_sha256': digest(index_path.read_bytes()),
    'files': [{'path': p, 'sha256': digest((ROOT / p).read_bytes()),
               'bytes': (ROOT / p).stat().st_size} for p in files],
    'proof_modules': 1,
    'roots': 4,
    'new_actual_local_exclusions': 0,
    'complete_global_cover': False,
    'new_zero_proportion_proven': False,
    'independent_Nanoda_replayed': False
}
sync_path = HERE / 'window_scalar_sector_sync_files.json'
sync_path.write_text(json.dumps(sync, indent=2) + '\n', encoding='utf8')
print(json.dumps({'proof_modules': 1, 'roots': 4, 'files': len(files),
                  'source_sha256': digest(raw),
                  'index_sha256': digest(index_path.read_bytes()),
                  'sync_sha256': digest(sync_path.read_bytes())}))
