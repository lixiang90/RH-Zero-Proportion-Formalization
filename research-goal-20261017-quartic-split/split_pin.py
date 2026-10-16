"""Freeze one exact covariance split and the two bounded numerical failures."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;OUT=HERE/'split-files.json'
def record(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def main():
    assert not OUT.exists();files=sorted([p for p in HERE.iterdir() if p.is_file() and p!=OUT],key=lambda p:p.name);deps={}
    for name in ['split-model.json','split-replay.json','split-cone-minus.json','split-cone-plus.json']:
        doc=json.loads((HERE/name).read_bytes());pins=doc['source_sha256_start'];assert pins==doc['source_sha256_end']
        for relative,h in pins.items():
            p=ROOT/relative;item=record(p);assert item['sha256']==h
            if p.parent!=HERE:deps[relative]=item
    out={'scope':__doc__,'package_files':[record(p) for p in files],'dependency_files':[deps[k] for k in sorted(deps)],
        'independent_read_only_replay':'research-goal-20261017-quartic-split/split_replay.py',
        'exact_disjunction_sides':2,'exact_old_point_quadratic_witness_values':['-1','-1'],
        'solver_calls':2,'solver_time_limit_seconds_each':45,'solver_maximum_iterations_each':10000,
        'recursive_splits':0,'extra_directions':0,'actual_scalar_samples':0,'Lean_invocations':0,
        'exact_child_exclusions':0,'complete_global_cover':False,'new_zero_proportion_proven':False}
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'manifest_sha256':record(OUT)['sha256'],'files':len(files),'dependencies':len(deps),'frozen_bytes':sum(p.stat().st_size for p in files)}))
if __name__=='__main__':main()
