"""Hash-only seal for a non-executed product-consumer design."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def rec(p):
 b=p.read_bytes();return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
files=[rec(HERE/n) for n in ['NOTE.zh.md','freeze_static.py']]
deps=[rec(ROOT/p) for p in [
 'research-goal-20261018-record-source-audit/snapshot/Solution.lean',
 'research-goal-20261018-record-source-audit/source-audit-files.json',
 'research-goal-20261018-stageB-static-contract/contract-files.json',
 'research-goal-20261018-record-baseline-replay/files.json']]
obj={'scope':'Static product-tree soundness and delivery-interface design; no implementation or pair scan.',
 'files':files,'dependencies':deps,'classification_runs':0,'product_runs':0,'pair_scans':0,
 'new_threshold_queries':0,'Lean_invocations':0,'solver_calls':0,
 'extra_source_size_known':False,'website_runtime_feasibility_known':False,
 'joint_floor_proved':False,'new_kappa_proved':False}
p=HERE/'review-files.json'
with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(obj,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps({'manifest':p.relative_to(ROOT).as_posix(),'sha256':rec(p)['sha256'],
 'owned_files':len(files),'owned_bytes':sum(r['bytes'] for r in files)},ensure_ascii=False))
