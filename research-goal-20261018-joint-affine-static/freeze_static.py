"""Seal paper-only joint affine derivation; no mathematical packet queries."""
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
 'research-goal-20261018-product-consumer-static/review-files.json']]
obj={'scope':'Paper-only extraction of existing actual term bounds into a joint affine certificate interface.',
 'files':files,'dependencies':deps,'packet_data_queries':0,'kernel_queries':0,
 'pair_scans':0,'new_bounds_computed':0,'optimizer_calls':0,'Lean_invocations':0,
 'joint_affine_floor_proved':False,'new_kappa_proved':False}
p=HERE/'review-files.json'
with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(obj,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps({'manifest':p.relative_to(ROOT).as_posix(),'sha256':rec(p)['sha256'],
 'owned_files':len(files),'owned_bytes':sum(r['bytes'] for r in files)},ensure_ascii=False))
