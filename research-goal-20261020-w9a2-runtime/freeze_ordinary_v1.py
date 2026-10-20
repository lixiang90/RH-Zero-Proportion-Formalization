"""Root freeze for the single-line Core proof repair; no compiler is called."""
from pathlib import Path
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]
def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):
    return json.loads(Path(p).read_text(encoding='utf-8'))
def pin(p):
    return {'path':p.relative_to(ROOT).as_posix(),'sha256':sha(p)}

oldgate=ROOT/'research-goal-20261016/gates/w9a2-ordinary-v0-20261020.json'
assert sha(oldgate)=='3960ea16d3ef7b2bf7d91453e95ec77aa143aee295ca655df0a45c01661d0533'
gate=load(oldgate)
repair=ROOT/'research-goal-20261020-w9a2-core-repair-v1'
manifest=repair/'files.json'
for row in load(manifest)['files']:
    p=repair/row['path']
    assert p.is_relative_to(repair) and sha(p)==row['sha256'], row['path']
newfull=repair/'canonical-full/StructuralW9A220261020/Core.lean'
newcore=repair/'development-split/StructuralW9A220261020/Core.lean'
oldfull=ROOT/'StructuralW9A220261020/Core.lean'
oldcore=ROOT/'research-goal-20261020-w9a2-formal-static-review/development-split/StructuralW9A220261020/Core.lean'
before='      simpa only [qTargetFrom, hs, ↓reduceIte] using h'.encode()
after='      simpa only [qTargetFrom, hs, Bool.false_eq_true, ↓reduceIte] using h'.encode()
for old,new in [(oldfull,newfull),(oldcore,newcore)]:
    raw=old.read_bytes()
    assert raw.count(before)==1 and raw.replace(before,after)==new.read_bytes()
assert sha(newfull)=='c2af225175f9a5ab14d2ba2612714a21e0613f66107a1d75b9d47bf1c77ba02a'
assert sha(newcore)=='26e23c7fc4fbae33bdfff446901eaeb0f22f0f08fe13fa4e326541565a25279f'
job=ROOT/'tmp/w9a2-20261020/candidate-ordinary-v0'
assert load(job/'terminal.json')['passed'] is False
assert load(job/'StructuralW9A220261020_Core.receipt.json')['exit_code']==1
prefix=load(job/'StructuralW9A220261020_Prefix.receipt.json')
assert prefix['exit_code']==0 and prefix['ordinary_compile_passed'] and prefix['source_unchanged']
prefixolean=job/'lib/StructuralW9A220261020/Prefix.olean'
assert sha(prefixolean)==prefix['olean_sha256']=='e9bbc282004e9c95ed69c608a2a3ebff6e399425b662c71edcc2e90705d05bfd'
gate['reused_oleans'].append({**pin(prefixolean),'module_path':'StructuralW9A220261020/Prefix.olean'})
gate['targets']=gate['targets'][1:]
gate['targets'][0].update(source=newcore.relative_to(ROOT).as_posix(),
    source_root=(repair/'development-split').relative_to(ROOT).as_posix())
gate['source_files'] += [pin(p) for p in [oldgate, manifest, repair/'repair.json',
    newfull,newcore,job/'terminal.json',job/'StructuralW9A220261020_Prefix.receipt.json',
    job/'StructuralW9A220261020_Core.receipt.json',job/'StructuralW9A220261020_Core.log',Path(__file__)]]
gate.update(work_directory='tmp/w9a2-20261020/candidate-ordinary-v1',
    scope='One explicitly reviewed same-theorem single-line Bool simplification repair, then Core/Graph/Localization/Counting/Final ordinary development verification.',
    candidate_compiler_runs_before_this_gate=1,
    root_observed_previous_parent_session=68239,root_observed_previous_parent_exit_code=1,
    repair_changes='Only Bool.false_eq_true added to one simp list; no theorem statement, numerical certificate, state, cost, graph, cursor or axiom changes.',
    unchanged_passing_development_Prefix_reused=True,
    known_limits=['Development reuse of exact passing Prefix and trusted ChallengeDeps only; no fullchain/cold/Comparator/Nano/website claim.',
                  'All finite checks in repaired Core must still execute; first error stops this new batch.'])
for row in gate['source_files']+gate['reused_oleans']:
    assert sha(ROOT/row['path'])==row['sha256'],row['path']
out=ROOT/'research-goal-20261016/gates/w9a2-ordinary-v1-20261020.json'
with out.open('x',encoding='utf-8',newline='\n') as f:
    json.dump(gate,f,indent=2)
    f.write('\n')
print(json.dumps({'gate':out.relative_to(ROOT).as_posix(),'sha256':sha(out),
                  'source_and_reused_pins':len(gate['source_files'])+len(gate['reused_oleans'])}))
