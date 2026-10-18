"""Hash-only seal for a static WZ dependency comparison; exclusive outputs."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def rec(p):
 b=p.read_bytes();return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
comparison=json.loads((HERE/'comparison.json').read_text(encoding='utf-8'))
for r in comparison['source_records']:
 assert rec(ROOT/r['path'])==r
files=[rec(HERE/n) for n in ['compare_static.py','comparison.json','NOTE.zh.txt','freeze_addendum.py']]
deps=[rec(ROOT/r) for r in ['research-goal-20261018-record-source-audit/source-audit-files.json',
 'research-goal-20261018-record-source-audit/snapshot/Solution.lean',
 'research-goal-20261018-record-source-audit/extract_static.py',
 'formal/upstream/ajp88-reweighted-nine-point.lean','scripts/finite_margin_20261015.py']]
obj={'scope':'Static WZ/coverChk dependency closure comparison only; not a new true-COV replay receipt.',
 'files':files,'dependencies':deps,'declarations_compared':comparison['declaration_count'],
 'identical_after_normalization':comparison['same_count'],
 'other_differences_only_profile_magnitude_literals':True,
 'new_true_COV_replayed':False,'new_floor_proved':False,'Lean_invocations':0,
 'solver_calls':0,'new_kernel_sampling_calls':0,'leaf_payload_decoded':False}
p=HERE/'addendum-files.json'
with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(obj,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps({'manifest':p.relative_to(ROOT).as_posix(),'sha256':rec(p)['sha256'],
                  'owned_files':len(files),'owned_bytes':sum(r['bytes'] for r in files)},ensure_ascii=False))
