"""Freeze one exact midpoint diagnostic for the complete eight-swap family."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;OUT=HERE/'swap-family-files.json'
def record(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def main():
    assert not OUT.exists();files=sorted([p for p in HERE.iterdir() if p.is_file() and p!=OUT],key=lambda p:p.name);deps={}
    for name in ['swap-family-static.json','swap-family-replay.json']:
        doc=json.loads((HERE/name).read_bytes());assert doc['source_sha256_start']==doc['source_sha256_end']
        for relative,h in doc['source_sha256_start'].items():
            p=ROOT/relative;item=record(p);assert item['sha256']==h
            if p.parent!=HERE:deps[relative]=item
    p=ROOT/'StructuralGoal20261016/WindowMinimizerCover.lean';deps[p.relative_to(ROOT).as_posix()]=record(p)
    out={'scope':__doc__,'package_files':[record(p) for p in files],'dependency_files':[deps[k] for k in sorted(deps)],
        'fixed_maps':8,'negative_midpoint_maps':4,'optimizer_calls':0,'new_moment_model_built':False,
        'Lean_invocations':0,'cell_exclusion_proven':False,'new_zero_proportion_proven':False}
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'manifest_sha256':record(OUT)['sha256'],'files':len(files),'dependencies':len(deps)}))
if __name__=='__main__':main()
