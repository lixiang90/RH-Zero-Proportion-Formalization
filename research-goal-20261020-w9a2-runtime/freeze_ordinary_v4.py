"""Root-review same reflection inequality; reuse exact passing Graph."""
from pathlib import Path
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p): return json.loads(Path(p).read_text(encoding='utf-8'))
def pin(p): return {'path':p.relative_to(ROOT).as_posix(),'sha256':sha(p)}
oldgate=ROOT/'research-goal-20261016/gates/w9a2-ordinary-v3-20261020.json'
assert sha(oldgate)=='8c890760d99414bccf6357571e85b1c1857e192d58af8fa41c9232ada6fcdde1'
gate=load(oldgate)
repair=ROOT/'research-goal-20261020-w9a2-localization-repair-v1'
manifest=repair/'files.json'
assert sha(manifest)=='e68e29c644e019de387e8570db5c86c9af80cc9fc9a13224e928c6e3d2f1fd31'
for row in load(manifest)['files']:
    p=repair/row['path'];assert p.is_relative_to(repair) and sha(p)==row['sha256']
old=ROOT/'StructuralW9A220261020/Localization.lean'
new=repair/'StructuralW9A220261020/Localization.lean'
raw=old.read_bytes();eol=b'\r\n' if b'\r\n' in raw else b'\n'
before=b'      simpa only [reverse8] using (le_of_lt (lt_of_not_ge ho))'
after='      change g 7 ≤ g 0'.encode()+eol+b'      exact le_of_lt (lt_of_not_ge ho)'
assert raw.count(before)==1 and raw.replace(before,after)==new.read_bytes()
assert sha(new)=='f4d32498996dd5f2781cdac1b17531c02757467dc62fae4e5b88d7d675842fd4'
job=ROOT/'tmp/w9a2-20261020/candidate-ordinary-v3'
assert not load(job/'terminal.json')['passed']
assert load(job/'StructuralW9A220261020_Localization.receipt.json')['exit_code']==1
graph=load(job/'StructuralW9A220261020_Graph.receipt.json')
assert graph['exit_code']==0 and graph['ordinary_compile_passed'] and graph['source_unchanged']
olean=job/'lib/StructuralW9A220261020/Graph.olean'
assert sha(olean)==graph['olean_sha256']=='9bfb52462f64be80158c143ac110fa2b0b23ca8c8577f37ea067280875ab4e0e'
gate['reused_oleans'].append({**pin(olean),'module_path':'StructuralW9A220261020/Graph.olean'})
gate['targets']=gate['targets'][1:]
gate['targets'][0].update(source=new.relative_to(ROOT).as_posix(),source_root=repair.relative_to(ROOT).as_posix())
gate['source_files'] += [pin(p) for p in [oldgate,manifest,new,job/'terminal.json',
    job/'StructuralW9A220261020_Graph.receipt.json',job/'StructuralW9A220261020_Localization.receipt.json',
    job/'StructuralW9A220261020_Localization.log',Path(__file__)]]
gate.update(work_directory='tmp/w9a2-20261020/candidate-ordinary-v4',
    scope='Same-hor Localization proof-only change of definitional reflected endpoints, then Localization/Counting/Final ordinary verification.',
    candidate_compiler_runs_before_this_gate=4,
    root_observed_previous_parent_session=46495,root_observed_previous_parent_exit_code=1,
    repair_changes='Only replace one simpa by definitional change g7<=g0 and the identical original inequality term; no hypotheses or mathematical data changes.',
    unchanged_passing_development_Graph_reused=True)
for row in gate['source_files']+gate['reused_oleans']:
    assert sha(ROOT/row['path'])==row['sha256'],row['path']
out=ROOT/'research-goal-20261016/gates/w9a2-ordinary-v4-20261020.json'
with out.open('x',encoding='utf-8',newline='\n') as f:
    json.dump(gate,f,indent=2);f.write('\n')
print(json.dumps({'gate':out.relative_to(ROOT).as_posix(),'sha256':sha(out),'pins':len(gate['source_files'])+len(gate['reused_oleans'])}))
