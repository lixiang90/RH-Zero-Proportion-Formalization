"""Seal a static Stage B design, never classify or evaluate a threshold."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def rec(p):
 b=p.read_bytes();return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
files=[rec(HERE/n) for n in ['PLAN.zh.md','freeze_contract.py']]
deps=[rec(ROOT/p) for p in [
 'research-goal-20261018-record-source-audit/source-audit-files.json',
 'research-goal-20261018-record-source-audit/snapshot/Solution.lean',
 'research-goal-20261018-record-source-audit/static-inventory.json',
 'research-goal-20261018-record-overlap-static/review-files.json',
 'research-goal-20261018-record-overlap-static/static-receipt.json',
 'research-goal-20261018-record-wz-static-addendum/addendum-files.json']]
obj={'scope':'Static contract only, not an implemented or run Stage B classifier.',
 'files':files,'dependencies':deps,'tau_numerator':'893916123055294719',
 'denominator':'100000000000000000000','separation':'17/20',
 'numeric_witness_count_expected':13046,'reflection_count_expected':595,
 'domain':'all arbitrary separated windows h>=17/20, F9(h)<tau; no minimizer assumption',
 'classifications_run':0,'new_threshold_queries':0,'pair_scans':0,
 'Lean_invocations':0,'kernel_sampling_calls':0,'solver_calls':0,
 'exceptions_already_complete':False,'joint_floor_proved':False,'new_kappa_proved':False,
 'future_execution_requires_separately_frozen_StageA_complete_replay':True}
p=HERE/'contract-files.json'
with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(obj,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps({'manifest':p.relative_to(ROOT).as_posix(),'sha256':rec(p)['sha256'],
                  'owned_files':len(files),'owned_bytes':sum(r['bytes'] for r in files)},ensure_ascii=False))
