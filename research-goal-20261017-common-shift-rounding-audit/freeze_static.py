"""Seal a static common-shift derivation and one exact metadata replay only."""
from pathlib import Path
import hashlib
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
OUT=HERE/'rounding-audit-files.json'

def record(p):
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,
            'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}

assert not OUT.exists()
receipt=json.loads((HERE/'metadata-replay.json').read_bytes())
assert receipt['passed']
assert receipt['source_sha256_start']==receipt['source_sha256_end']
for name,h in receipt['source_sha256_start'].items():
    assert record(ROOT/name)['sha256']==h
assert all(c['maximum_ceiling_upper']==32 for c in receipt['cases'])
for key in ['kernel_evaluations','new_table_entries','tree_or_point_records_scanned',
            'solver_calls','Lean_invocations']:
    assert receipt[key]==0
refs=['StructuralGoal20261016/WindowMinimizerCover.lean',
      'StructuralGoal20261016/WindowGlobalCompetitor.lean',
      'StructuralGoal20261016/WindowGapEnergy.lean',
      'StructuralW10Followup20261016/NewLedger.lean',
      'StructuralGoal20261016/WindowKernel.lean',
      'StructuralGoal20261016/WindowNormalizedJets.lean',
      'StructuralGoal20261016/WindowFixedTablesAll.lean',
      'research-goal-20261016/cover_competitor_diagnostic.py',
      'research-goal-20261016/window_phase_lattice_rigidity_note.txt',
      'research-goal-20261016/window_phase_hermitian_audit.txt']
files=[p for p in HERE.iterdir() if p.is_file() and p!=OUT]
assert len(files)==4 and all(p.stat().st_size<40*1024**2 for p in files)
result={'scope':__doc__,
        'package_files':[record(p) for p in sorted(files)],
        'dependency_files':[record(ROOT/name) for name in refs],
        'finite_convex_combination_derivation_valid_as_written':True,
        'global_minimum_over_entire_orthant_is_required':True,
        'shared_shift_gives_at_most_ten_feasible_configurations':True,
        'independent_fraction_cutoff_metadata_passed':True,
        'targets':['11/1250','221/25000'],'maximum_integer_centre':32,
        'ordinary_integer_translation_repetition':False,
        'new_floating_experiments':0,'kernel_evaluations':0,
        'new_tree_or_point_scans':0,'solver_calls':0,'Lean_invocations':0,
        'new_global_floor_proven':False,'new_inequality_Lean_proven':False,
        'tree_reduction_or_runtime_saving_measured':False,
        'website_source_or_runtime_contract_met':False,
        'new_unconditional_zero_proportion_proven':False,
        'website_submission_ready':False,
        'further_experiment_automatically_authorized':False}
OUT.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
print(json.dumps({'pin_sha256':record(OUT)['sha256'],
                  'package_files':len(files),
                  'package_bytes':sum(p.stat().st_size for p in files),
                  'reference_sources':len(refs)}))
