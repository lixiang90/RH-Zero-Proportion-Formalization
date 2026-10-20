"""Authorize one qualification-only Counting repair and downstream Final check."""
from pathlib import Path
import hashlib, json
ROOT=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text(encoding='utf-8'))
def pin(p):return dict(path=p.relative_to(ROOT).as_posix(),sha256=sha(p))
oldgate=ROOT/'research-goal-20261016/gates/w9a2-ordinary-v5-20261020.json'
assert sha(oldgate)=='5a928e8066bd0c8a1bb3cd9e28028b9c995dd40728eed3e72612f9ca8f086d0e'
gate=load(oldgate);repair=ROOT/'research-goal-20261020-w9a2-counting-repair-v1'
manifest=repair/'files.json'
for r in load(manifest)['files']:
    p=repair/r['path'];assert p.is_relative_to(repair) and sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
old=ROOT/'StructuralW9A220261020/Counting.lean';new=repair/'StructuralW9A220261020/Counting.lean'
assert sha(old)=='163fbaae81c9afd492cdfd5c66dd2848f1d1e03ac0af6ae3774a7cc619c631d5'
raw=old.read_bytes();assert raw.count(b'wfun')==3
assert new.read_bytes()==raw.replace(b'wfun',b'Zeta23Ext.Bridge.wfun')
assert new.stat().st_size==old.stat().st_size+51
count_target=load(ROOT/'research-goal-20261016/gates/w9a2-ordinary-v4-20261020.json')['targets'][1]
assert count_target['module']=='StructuralW9A220261020.Counting'
count_target.update(source=new.relative_to(ROOT).as_posix(),source_root=repair.relative_to(ROOT).as_posix())
gate['targets']=[count_target,*gate['targets']]
gate['reused_oleans']=[r for r in gate['reused_oleans'] if r['module_path']!='StructuralW9A220261020/Counting.olean']
gate['source_files'] += [pin(p) for p in [manifest,new,ROOT/'research-goal-20261020-w9a2-fullchain-v1-terminal/files.json',Path(__file__)]]
gate.update(work_directory='tmp/w9a2-20261020/candidate-ordinary-v6',scope='Three explicit Bridge.wfun qualifications only; recompile Counting and unchanged Final with twelve printed roots.',root_observed_previous_parent_session=68653,root_observed_previous_parent_exit_code=1,repair_changes='Exactly three bare wfun identifiers receive the Zeta23Ext.Bridge prefix (+51 bytes); all statements, proof tactics, numerical data, imports and axiom policy unchanged.',unchanged_passing_development_Localization_Counting_reused=False,unchanged_passing_development_Localization_reused=True,automatic_repairs_or_retries=0)
for r in gate['source_files']+gate['reused_oleans']:assert sha(ROOT/r['path'])==r['sha256']
out=ROOT/'research-goal-20261016/gates/w9a2-ordinary-v6-20261020.json'
with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(gate,f,indent=2);f.write('\n')
print(json.dumps(dict(gate=out.relative_to(ROOT).as_posix(),sha256=sha(out),source_sha256=sha(new),compiler_started=False)))
