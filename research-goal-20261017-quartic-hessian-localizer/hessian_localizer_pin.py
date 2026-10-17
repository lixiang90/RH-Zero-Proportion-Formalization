"""Freeze one unsuccessful static affine-position Hessian separation test."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;OUT=HERE/'hessian-localizer-files.json'
def record(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def main():
    assert not OUT.exists();files=sorted([p for p in HERE.iterdir() if p.is_file() and p!=OUT],key=lambda p:p.name);deps={}
    for name in ['hessian-localizer-static.json','hessian-localizer-replay.json']:
        doc=json.loads((HERE/name).read_bytes());assert doc['source_sha256_start']==doc['source_sha256_end']
        for relative,h in doc['source_sha256_start'].items():
            p=ROOT/relative;item=record(p);assert item['sha256']==h
            if p.parent!=HERE:deps[relative]=item
    out={'scope':__doc__,'package_files':[record(p) for p in files],'dependency_files':[deps[k] for k in sorted(deps)],
        'matrix_size':90,'eigh_calls':1,'rational_direction_attempts':0,'solver_calls':0,'Lean_invocations':0,
        'exact_pseudomoment_separation':False,'cell_exclusion_proven':False,'new_zero_proportion_proven':False}
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'manifest_sha256':record(OUT)['sha256'],'files':len(files),'dependencies':len(deps)}))
if __name__=='__main__':main()
