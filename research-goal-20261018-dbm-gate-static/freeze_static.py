"""Hash-only seal of static DBM contract review. No pair or query execution."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def rec(p):
 b=p.read_bytes();return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
files=[rec(HERE/n) for n in ['NOTE.zh.md','freeze_static.py']]
deps=[rec(ROOT/p) for p in [
 'research-goal-20261018-product-consumer-static/review-files.json',
 'research-goal-20261018-stageB-static-contract/contract-files.json',
 'research-goal-20261018-record-source-audit/snapshot/Solution.lean']]
obj={'scope':'Static fixed DBM opportunity gate review only; execution not authorized by this receipt.',
 'files':files,'dependencies':deps,'expected_cells_each_side':1187,
 'orientations':4,'expected_orientation_pairs':5635876,'directed_input_edges_per_pair':153,
 'pair_scans':0,'classification_runs':0,'new_threshold_queries':0,'Lean_invocations':0,
 'solver_calls':0,'mathematical_joint_gate_passed':False,'website_budget_passed':False}
p=HERE/'review-files.json'
with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(obj,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps({'manifest':p.relative_to(ROOT).as_posix(),'sha256':rec(p)['sha256'],
 'owned_files':len(files),'owned_bytes':sum(r['bytes'] for r in files)},ensure_ascii=False))
