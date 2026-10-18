"""Seal paper global checker/encoding contract, with no data scan or solver."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def rec(p):
 b=p.read_bytes();return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
files=[rec(HERE/n) for n in ['CONTRACT.zh.md','freeze_static.py']]
deps=[rec(ROOT/p) for p in [
 'research-goal-20261018-record-source-audit/snapshot/Solution.lean',
 'research-goal-20261018-joint-affine-flow-proof/proof-files.json',
 'research-goal-20261018-stageE-static-review/review-files.json',
 'research-goal-20261018-stageF-static-review/review-files.json',
 'research-goal-20261018-product-consumer-static/review-files.json',
 'research-goal-20261018-joint-size-opportunity/files.json',
 'research-goal-20261018-record-recheck/files.json']]
obj={'scope':'Paper-only complete fixed-model checker contract, small-minor/basis/circuit encoding review.',
 'files':files,'dependencies':deps,'paper_cross_review':'joint_gluing_review message, no data/computation',
 'fixed_rows_per_chart':155,'ordered_rows_max':2,'gauge_dimension':9,
 'square_minor_absolute_bound':4,'primitive_empty_weights':[1,2,3,4],
 'global_classification_runs':0,'new_statistics_scans':0,'LP_calls':0,
 'kernel_queries':0,'Lean_invocations':0,'G_authorized_by_this_packet':False,
 'global_floor_proved':False,'website_size_or_time_passed':False}
p=HERE/'contract-files.json'
with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(obj,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps({'manifest':p.relative_to(ROOT).as_posix(),'sha256':rec(p)['sha256'],
 'owned_files':len(files),'owned_bytes':sum(r['bytes'] for r in files)},ensure_ascii=False))
