"""Seal static Stage E logic. Does not evaluate margins or pair conditions."""
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
 'research-goal-20261018-product-consumer-static/review-files.json',
 'research-goal-20261018-stageB-classification/files.json',
 'research-goal-20261018-stageB-independent/audit-files.json',
 'research-goal-20261018-stageD-independent/audit-files.json']]
obj={'scope':'Static global logic of exact whole-cell margin payment followed by DBM only for underpaid pairs.',
 'files':files,'dependencies':deps,'model':'exact-Mi-not-Nat-floor',
 'c9_numerator':'893616123055294719','tau_numerator':'893916123055294719',
 'SA':'100000000000000000000','kappa':'335544320000000000',
 'payment_test':'Mi+Mj >= kappa*(tauN-c9N)',
 'expected_cells_each_side':1187,'expected_orientation_pairs':5635876,
 'E_runs':0,'margin_queries':0,'pair_scans':0,'kernel_queries':0,
 'optimizer_calls':0,'Lean_invocations':0,'E_gate_passed':False,
 'joint_floor_Lean_proved':False,'new_kappa_proved':False}
p=HERE/'review-files.json'
with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(obj,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps({'manifest':p.relative_to(ROOT).as_posix(),'sha256':rec(p)['sha256'],
 'owned_files':len(files),'owned_bytes':sum(r['bytes'] for r in files)},ensure_ascii=False))
