"""Freeze joint-window counting design, one exact obstruction, one fixed LP."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;OUT=HERE/'multiwindow-files.json'
def record(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def main():
    assert not OUT.exists();files=sorted([p for p in HERE.iterdir() if p.is_file() and p!=OUT],key=lambda p:p.name);deps={}
    for name in ['multiwindow-diagnostic.json','multiwindow-fixed-pair-pilot.json','multiwindow-same-ledger-obstruction.json','multiwindow-replay.json']:
        doc=json.loads((HERE/name).read_bytes());pins=doc['source_sha256_start'];assert pins==doc['source_sha256_end']
        for relative,h in pins.items():
            p=ROOT/relative;item=record(p);assert item['sha256']==h
            if p.parent!=HERE:deps[relative]=item
    for name in ['research-goal-20261017-quartic/quartic-files.json','research-goal-20261017-quartic-split/split-files.json',
        'formal/upstream/ajp88-reweighted-nine-point.lean']:
        p=ROOT/name;deps[name]=record(p)
    out={'scope':__doc__,'package_files':[record(p) for p in files],'dependency_files':[deps[k] for k in sorted(deps)],
        'read_only_independent_replay':'research-goal-20261017-multiwindow/multiwindow_replay.py',
        'same_ledger_exact_matrix_size':24,'same_ledger_variance_ratio_upper':'11/10',
        'fixed_profile_pairs':1,'finite_sample_LP_calls':1,'LP_time_limit_seconds':45,'sample_points':29171,
        'additional_adversaries':0,'recursive_cover_jobs':0,'Lean_invocations':0,
        'actual_new_profile_AdmWindow_and_PV_premises_discharged':False,'different_ledger_family_excluded':False,
        'global_floor_proven':False,'new_zero_proportion_proven':False}
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'manifest_sha256':record(OUT)['sha256'],'files':len(files),'dependencies':len(deps),'frozen_bytes':sum(p.stat().st_size for p in files)}))
if __name__=='__main__':main()
