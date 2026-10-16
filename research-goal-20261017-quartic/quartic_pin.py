"""Freeze the completed quartic static model and exact relaxation obstruction."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;OUT=HERE/'quartic-files.json'
def record(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def main():
    assert not OUT.exists()
    files=sorted([p for p in HERE.iterdir() if p.is_file() and p!=OUT],key=lambda p:p.name)
    deps={}
    for name in ['quartic-build.json','quartic-replay.json','quartic-cone.json','quartic-rankone.json','quartic-exact-primal.json','quartic-result-replay.json']:
        doc=json.loads((HERE/name).read_bytes());pins=doc.get('source_sha256_start',doc.get('input_sha256_start'))
        for relative,h in pins.items():
            p=ROOT/relative;item=record(p);assert item['sha256']==h
            if p.parent!=HERE:deps[relative]=item
    p=ROOT/'research-20261016-w10-cert/independent_integer_audit.py';deps[p.relative_to(ROOT).as_posix()]=record(p)
    result={'scope':__doc__,'package_files':[record(p) for p in files],
        'dependency_files':[deps[k] for k in sorted(deps)],
        'independent_replays':['research-goal-20261017-quartic/quartic_replay.py','research-goal-20261017-quartic/quartic_result_replay.py'],
        'solver_calls':1,'solver_time_limit_seconds':45,'solver_iteration_limit':10000,'solver_cases':1,
        'exact_result':'unadjusted rational feasible point of the fixed shared degree-four outer relaxation',
        'exact_rows':5795,'strict_positive_PSD_blocks':47,'rank_one_mean_diagnostic_failed_rows':6,
        'actual_F_or_KKT_counterexample':False,'Lean_invocations':0,'complete_global_cover':False,'new_zero_proportion_proven':False}
    OUT.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'manifest_sha256':record(OUT)['sha256'],'files':len(files),'dependencies':len(deps),'frozen_bytes':sum(p.stat().st_size for p in files)}))
if __name__=='__main__':main()
