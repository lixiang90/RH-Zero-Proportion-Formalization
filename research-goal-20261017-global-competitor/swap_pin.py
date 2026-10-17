"""Freeze the one fixed swap midpoint comparison and its independent replay."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;OUT=HERE/'swap-files.json'
def record(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def main():
    assert not OUT.exists();files=sorted([p for p in HERE.iterdir() if p.is_file() and p!=OUT],key=lambda p:p.name);deps={}
    for name in ['swap-midpoint-static.json','swap-replay.json']:
        doc=json.loads((HERE/name).read_bytes());assert doc['source_sha256_start']==doc['source_sha256_end']
        for relative,h in doc['source_sha256_start'].items():
            p=ROOT/relative;item=record(p);assert item['sha256']==h
            if p.parent!=HERE:deps[relative]=item
    out={'scope':__doc__,'package_files':[record(p) for p in files],'dependency_files':[deps[k] for k in sorted(deps)],
        'maps_tested':1,'map':'swap(g5,g6)','midpoint_difference_strictly_positive':True,'optimizer_calls':0,
        'new_moment_model_built':False,'Lean_invocations':0,'cell_exclusion_proven':False,'new_zero_proportion_proven':False}
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'manifest_sha256':record(OUT)['sha256'],'files':len(files),'dependencies':len(deps)}))
if __name__=='__main__':main()
