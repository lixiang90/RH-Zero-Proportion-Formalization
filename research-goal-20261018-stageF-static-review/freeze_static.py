"""Seal a paper-only fixed LP contract review. Never solve or inspect pair data."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def rec(p):
 b=p.read_bytes();return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
files=[rec(HERE/n) for n in ['NOTE.zh.md','freeze_static.py']]
deps=[rec(ROOT/p) for p in [
 'research-goal-20261018-record-source-audit/snapshot/Solution.lean',
 'research-goal-20261018-joint-affine-flow-proof/proof-files.json',
 'research-goal-20261018-joint-transshipment-static/review-files.json',
 'research-goal-20261018-stageE-static-review/review-files.json']]
obj={'scope':'Static sign, scale, boundedness and certificate-support review for one fixed F LP.',
 'files':files,'dependencies':deps,'pair_ids':[1,5],'orientations':['id','id'],
 'rows':155,'gauge_reduced_dimension':9,'candidate_floor_numerator':'893766123055294719',
 'optimum_dual_support_bound':9,'empty_Farkas_support_bound':10,
 'new_pair_evaluations':0,'LP_calls':0,'kernel_queries':0,'Lean_invocations':0,
 'F_result_known':False,'whole_joint_floor_proved':False,'website_budget_passed':False}
p=HERE/'review-files.json'
with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(obj,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps({'manifest':p.relative_to(ROOT).as_posix(),'sha256':rec(p)['sha256'],
 'owned_files':len(files),'owned_bytes':sum(r['bytes'] for r in files)},ensure_ascii=False))
