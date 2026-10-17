"""Freeze one fixed positive-divided swap67 integral and independent audit."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
AUDIT=ROOT/'research-goal-20261017-swap67-divided-audit';OUT=HERE/'divided-files.json'
def rec(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
assert not OUT.exists();doc=json.loads((HERE/'divided-static.json').read_bytes());ap=json.loads((AUDIT/'audit-files.json').read_bytes())
assert doc['source_sha256_start']==doc['source_sha256_end'] and not doc['latest_exact714_separated_by_necessary_row']
files=[p for p in HERE.iterdir() if p.is_file() and p!=OUT]+[p for p in AUDIT.iterdir() if p.is_file()];names={p.relative_to(ROOT).as_posix() for p in files};deps={}
for name,h in doc['source_sha256_start'].items():
    r=rec(ROOT/name);assert r['sha256']==h
    if name not in names:deps[name]=r
for r in ap.get('files',ap.get('package_files',[])):
    assert rec(ROOT/r['path'])['sha256']==r['sha256']
out={'scope':__doc__,'package_files':[rec(p) for p in sorted(files,key=lambda p:p.relative_to(ROOT).as_posix())],
    'dependency_files':[deps[k] for k in sorted(deps)],'same_fixed_swap_zero_based':[6,7],'positive_function_lower_bound':'117/32768',
    'theta_integrated_exactly':True,'independent_stdlib_replay_passed':True,'latest_exact714_separated':False,
    'solver_calls':0,'Lean_invocations':0,'cell_exclusion_proven':False,'new_zero_proportion_proven':False}
OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
print(json.dumps({'manifest_sha256':rec(OUT)['sha256'],'files':len(files),'dependencies':len(deps)}))
