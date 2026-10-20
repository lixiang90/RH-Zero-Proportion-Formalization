"""Same-definition final bridge; exact passing Localization and Counting reuse."""
from pathlib import Path
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p): return json.loads(Path(p).read_text(encoding='utf-8'))
def pin(p): return {'path':p.relative_to(ROOT).as_posix(),'sha256':sha(p)}
oldgate=ROOT/'research-goal-20261016/gates/w9a2-ordinary-v4-20261020.json'
assert sha(oldgate)=='9ed847edf10614f5bada1791551ed2874771add9b5532d57bb8acfb365047ac4'
gate=load(oldgate);repair=ROOT/'research-goal-20261020-w9a2-final-repair-v1';manifest=repair/'files.json'
assert sha(manifest)=='c9a946281b01f9f8d1159345a475a831eacc92fea7e9e1ca7bf13a1332f525e8'
for row in load(manifest)['files']:
    p=repair/row['path'];assert p.is_relative_to(repair) and sha(p)==row['sha256']
old=ROOT/'StructuralW9A220261020/Final.lean';new=repair/'StructuralW9A220261020/Final.lean'
raw=old.read_bytes();eol=b'\r\n' if b'\r\n' in raw else b'\n'
for side,var,hyp in [('left','s','hs'),('right','t','ht')]:
    before=(f'    · simpa only [StructuralW9A220261020.Counting.{side}Gaps,'+eol.decode()+
            f'        StructuralW9A220261020.Graph.{side}Gaps] using {hyp}').encode()
    after=(f'    · change StructuralW9A220261020.Graph.StateAt'+eol.decode()+
           f'        (StructuralW9A220261020.Counting.{side}Gaps g) {var}'+eol.decode()+f'      exact {hyp}').encode()
    assert raw.count(before)==1;raw=raw.replace(before,after)
assert raw==new.read_bytes() and sha(new)=='ea99cc00802c2b3170a9b0c39b1f8b383e69f7c1ab76de851b9cd193c4353cf9'
job=ROOT/'tmp/w9a2-20261020/candidate-ordinary-v4';assert not load(job/'terminal.json')['passed']
assert load(job/'StructuralW9A220261020_Final.receipt.json')['exit_code']==1
extra=[oldgate,manifest,new,job/'terminal.json',job/'StructuralW9A220261020_Final.receipt.json',job/'StructuralW9A220261020_Final.log',Path(__file__)]
for name,expected in [('Localization','2870323379cea6b2d04deaef60fbce8e8d9f18e42ebb7f71ea34cac91e96dc8c'),
                      ('Counting','2676fc58f762732c514b8942bf75b1222d1c90d7703f23279618587ddeb651c2')]:
    receipt=job/f'StructuralW9A220261020_{name}.receipt.json';r=load(receipt)
    assert r['exit_code']==0 and r['ordinary_compile_passed'] and r['source_unchanged']
    if name=='Counting':assert r['axiom_audit_passed'] and len(r['observed_axioms'])==5
    olean=job/f'lib/StructuralW9A220261020/{name}.olean';assert sha(olean)==r['olean_sha256']==expected
    gate['reused_oleans'].append({**pin(olean),'module_path':f'StructuralW9A220261020/{name}.olean'})
    extra.append(receipt)
gate['targets']=gate['targets'][2:]
assert len(gate['targets'])==1 and gate['targets'][0]['module'].endswith('.Final')
gate['targets'][0].update(source=new.relative_to(ROOT).as_posix(),source_root=repair.relative_to(ROOT).as_posix())
gate['source_files'] += [pin(p) for p in extra]
gate.update(work_directory='tmp/w9a2-20261020/candidate-ordinary-v5',
    scope='Only Final same-definition left/right window bridge repair and seven-root transitive axiom audit.',
    candidate_compiler_runs_before_this_gate=5,
    root_observed_previous_parent_session=90216,root_observed_previous_parent_exit_code=1,
    repair_changes='Only explicit definitional target change then exact original hs/ht at two proof branches. No statements, premises, mathematical data or axiom changes.',
    unchanged_passing_development_Localization_Counting_reused=True)
for row in gate['source_files']+gate['reused_oleans']:assert sha(ROOT/row['path'])==row['sha256']
out=ROOT/'research-goal-20261016/gates/w9a2-ordinary-v5-20261020.json'
with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(gate,f,indent=2);f.write('\n')
print(json.dumps({'gate':out.relative_to(ROOT).as_posix(),'sha256':sha(out),'pins':len(gate['source_files'])+len(gate['reused_oleans'])}))
