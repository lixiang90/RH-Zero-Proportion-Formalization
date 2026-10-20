"""Explicit one-attempt Graph simp-control correction; same frozen mathematics."""
from pathlib import Path
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p): return json.loads(Path(p).read_text(encoding='utf-8'))
def pin(p): return {'path':p.relative_to(ROOT).as_posix(),'sha256':sha(p)}
oldgate=ROOT/'research-goal-20261016/gates/w9a2-ordinary-v2-20261020.json'
assert sha(oldgate)=='59062ce669fcfc8e8a18e3367688f3f9e7d0eb8e9e1120fdbc2ab12f3ff57dac'
gate=load(oldgate)
repair=ROOT/'research-goal-20261020-w9a2-graph-repair-v2'
manifest=repair/'files.json'
assert sha(manifest)=='5e5162d27f6e99347c425b954135db00f4e729b53ba4a430c2b26b4a8eb186a9'
for row in load(manifest)['files']:
    p=repair/row['path'];assert p.is_relative_to(repair) and sha(p)==row['sha256']
old=ROOT/gate['targets'][0]['source']
new=repair/'StructuralW9A220261020/Graph.lean'
before=b'<;> simp only [Fin.reduceFinMk] <;> ring'
after=b'<;> (try simp only [Fin.reduceFinMk]) <;> ring'
assert old.read_bytes().count(before)==1 and old.read_bytes().replace(before,after)==new.read_bytes()
assert sha(new)=='2e259252f7fa993954bd52c4a6d6ec58594116a500a576910d6fa671d6521966'
job=ROOT/'tmp/w9a2-20261020/candidate-ordinary-v2'
assert load(job/'terminal.json')['passed'] is False
assert load(job/'StructuralW9A220261020_Graph.receipt.json')['exit_code']==1
gate['targets'][0].update(source=new.relative_to(ROOT).as_posix(),source_root=repair.relative_to(ROOT).as_posix())
gate['source_files'] += [pin(p) for p in [oldgate,manifest,new,job/'terminal.json',
    job/'StructuralW9A220261020_Graph.receipt.json',job/'StructuralW9A220261020_Graph.log',Path(__file__)]]
gate.update(work_directory='tmp/w9a2-20261020/candidate-ordinary-v3',
    scope='One explicitly reviewed parenthesized try around Fin normalization in Graph reverse_span, then Graph/Localization/Counting/Final ordinary verification.',
    candidate_compiler_runs_before_this_gate=3,
    root_observed_previous_parent_session=42867,root_observed_previous_parent_exit_code=1,
    repair_changes='Only tolerate no-progress in the explicit Fin simp, original ring still follows; same theorem and all graph/source bytes outside that line unchanged.')
for row in gate['source_files']+gate['reused_oleans']:
    assert sha(ROOT/row['path'])==row['sha256'],row['path']
out=ROOT/'research-goal-20261016/gates/w9a2-ordinary-v3-20261020.json'
with out.open('x',encoding='utf-8',newline='\n') as f:
    json.dump(gate,f,indent=2);f.write('\n')
print(json.dumps({'gate':out.relative_to(ROOT).as_posix(),'sha256':sha(out),
                  'source_and_reused_pins':len(gate['source_files'])+len(gate['reused_oleans'])}))
