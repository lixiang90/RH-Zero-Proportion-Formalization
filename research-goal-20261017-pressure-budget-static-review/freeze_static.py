"""Hash-only seal of a static logic review; no arithmetic replay or Lean."""
from pathlib import Path
import hashlib,json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def pin(p):
    b=p.read_bytes()
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),
            'sha256':hashlib.sha256(b).hexdigest()}

base=ROOT/'research-goal-20261017-pressure-budget'
receipt=json.loads((base/'receipt.json').read_text(encoding='utf-8'))
cap=json.loads((base/'family-cap.json').read_text(encoding='utf-8'))
assert cap['fixed_point_receipt_sha256']==pin(base/'receipt.json')['sha256']
assert receipt['script_sha256']==pin(base/'pressure_budget.py')['sha256']
assert cap['script_sha256']==pin(base/'budget_cap.py')['sha256']
deps=[base/n for n in ['receipt.json','family-cap.json','pressure_budget.py','budget_cap.py']]
deps += [ROOT/n for n in [
    'StructuralGoal20261016/WindowGapEnergy.lean',
    'StructuralGoal20261016/WindowMinimizerCover.lean',
    'StructuralGoal20261016/WindowGramExpansion.lean',
    'StructuralW10Followup20261016/NewLedger.lean',
    'research-goal-20261017-common-rounding/rounding-files.json',
    'research-goal-20261017-integer-adjacent-floor-audit/audit-files.json',
]]
obj={'scope':'Static logic review of the fixed whole-original-domain uniform scalar-affine-pressure budget no-go.',
     'files':[pin(HERE/'NOTE.zh.txt'),pin(Path(__file__))],
     'dependencies':[pin(p)for p in deps],
     'static_logic_review_passed':True,'numerical_replay_performed_by_this_review':False,
     'new_Lean_files':0,'Lean_invocations':0,'solver_calls':0,'new_numerical_budget_evaluations':0,
     'family_stopped':True,'continuous_floor_refuted':False,
     'complete_global_floor_proven':False,'new_unconditional_proportion_proven':False,
     'governance_files_modified':False,'main_round_counter_modified':False}
p=HERE/'review-files.json'
with p.open('x',encoding='utf-8',newline='\n')as f:
    json.dump(obj,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps({'manifest':p.relative_to(ROOT).as_posix(),'sha256':pin(p)['sha256'],
                  'owned_files':len(obj['files']),'owned_bytes':sum(r['bytes']for r in obj['files'])}))
