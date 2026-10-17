"""Freeze one fixed Q2 localizer's positive spectral hint, not exact PSD."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;OUT=HERE/'q2-files.json'
def record(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
assert not OUT.exists();doc=json.loads((HERE/'swap67-q2-localizer.json').read_bytes())
assert doc['eigh_calls']==1 and doc['integer_vector_attempts']==0 and not doc['new_exact714_separated']
assert doc['source_sha256_start']==doc['source_sha256_end']
files=[p for p in HERE.iterdir() if p.is_file() and p!=OUT];names={p.relative_to(ROOT).as_posix() for p in files};deps=[]
for name,h in doc['source_sha256_start'].items():
    r=record(ROOT/name);assert r['sha256']==h
    if name not in names:deps.append(r)
out={'scope':__doc__,'package_files':[record(p) for p in sorted(files,key=lambda p:p.name)],'dependency_files':deps,
    'one_fixed_swap_zero_based':[6,7],'one_eigh':True,'integer_vector_attempts':0,'negative_vector_found':False,
    'positive_floating_eigenvalues_are_not_exact_PSD':True,'independent_arithmetic_replay_separate_addon':True,
    'solver_calls':0,'Lean_invocations':0,'cell_exclusion_proven':False,'new_zero_proportion_proven':False}
OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
print(json.dumps({'manifest_sha256':record(OUT)['sha256'],'files':len(files),'dependencies':len(deps)}))
