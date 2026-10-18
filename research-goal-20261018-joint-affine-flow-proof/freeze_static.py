"""Seal exact paper algebra, never evaluate candidate affine values."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def rec(p):
 b=p.read_bytes();return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
files=[rec(HERE/n) for n in ['PROOF.zh.md','freeze_static.py']]
deps=[rec(ROOT/p) for p in [
 'research-goal-20261018-record-source-audit/snapshot/Solution.lean',
 'research-goal-20261018-joint-affine-static/review-files.json']]
obj={'scope':'Static exact source-form proof that faithful FS affine >= original floor on its original cell.',
 'files':files,'dependencies':deps,'data_queries':0,'affine_values_evaluated':0,
 'kernel_queries':0,'optimizer_calls':0,'pair_scans':0,'Lean_invocations':0,
 'new_Lean_lemma_verified':False,'new_joint_floor_proved':False}
p=HERE/'proof-files.json'
with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(obj,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps({'manifest':p.relative_to(ROOT).as_posix(),'sha256':rec(p)['sha256'],
 'owned_files':len(files),'owned_bytes':sum(r['bytes'] for r in files)},ensure_ascii=False))
