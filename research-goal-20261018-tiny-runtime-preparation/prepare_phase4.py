"""Final-only exact-term elaboration across the existing counting definitions."""
from pathlib import Path
import hashlib, json, difflib
ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent
def row(p):
    b=p.read_bytes()
    return dict(path=p.relative_to(ROOT).as_posix(),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(p,s):
    p.parent.mkdir(parents=True,exist_ok=True)
    with p.open('xb') as f:f.write(s if isinstance(s,bytes) else s.encode())
def dump(p,x):put(p,json.dumps(x,indent=2)+'\n')
p3=json.loads((HERE/'phase3-prepared.json').read_bytes())
oldp=ROOT/'StructuralS1RTiny20261018/Phase3/Final.lean'
old=oldp.read_text(encoding='utf-8')
assert old.count('  simpa only [ratio_exact] using h')==2
new=old.replace('  simpa only [ratio_exact] using h','  rw [← ratio_exact]\n  exact h')
src=ROOT/'StructuralS1RTiny20261018/Phase4/Final.lean'
put(src,new)
put(HERE/'phase4-final.diff',''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='Phase3/Final.lean',tofile='Phase4/Final.lean')))
runner=(HERE/'compile_phase3.py').read_text(encoding='utf-8').replace('phase3-v0','phase4-v0').replace('phase3-prepared.json','phase4-prepared.json').replace('tiny-current-s1R-final-phase3','tiny-current-s1R-final-phase4')
put(HERE/'compile_phase4.py',runner)
target=dict(p3['targets'][0]);target['module']='StructuralS1RTiny20261018/Phase4/Final'
gate=json.loads((HERE/'phase3-gate-template.json').read_bytes());gate.update(task='tiny-current-s1R-final-phase4',allowed_modules=[target['module']])
dump(HERE/'phase4-gate-template.json',gate)
deps=list(dict.fromkeys([ROOT/x['path'] for x in p3['dependencies']]+[oldp,HERE/'phase3-prepared.json',ROOT/'tmp/current-s1r-tiny-20261018/phase3-v0/Final.log',ROOT/'tmp/current-s1r-tiny-20261018/phase3-v0/Final.receipt.json',ROOT/'tmp/current-s1r-tiny-20261018/phase3-v0/terminal.json']))
prep=dict(p3)
prep.update(schema='tiny-final-exact-elaboration-phase4-v1',files=[row(p) for p in [src,Path(__file__),HERE/'compile_phase4.py',HERE/'phase4-final.diff',HERE/'phase4-gate-template.json']],dependencies=[row(p) for p in deps],targets=[target],only_explicit_function_equality_and_root_name_qualification=False,only_replace_simpa_by_rewrite_then_exact=True)
dump(HERE/'phase4-prepared.json',prep)
print(json.dumps(row(HERE/'phase4-prepared.json')))
