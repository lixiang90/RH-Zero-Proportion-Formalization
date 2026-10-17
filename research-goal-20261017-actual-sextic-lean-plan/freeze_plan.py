"""Freeze the static actual-interface/source-size plan; run no mathematical experiment."""
from pathlib import Path
import hashlib
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent


def row(p):
    raw=p.read_bytes()
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}


def main():
    report=json.loads((HERE/'static-inventory.json').read_bytes())
    assert report['source_sha256_start']==report['source_sha256_end']
    assert report['active_scalar_rows']==14562 and len(report['active_Gram_blocks'])==73
    assert report['literal_data_inventory']['weights_and_factors_decimal_array_bytes']==2270318
    dependencies={};historical_policy=[]
    for name,h in report['source_sha256_start'].items():
        if name=='research-goal-20261016/DIRECTION.zh.md':
            snapshot=ROOT/'research-goal-20261017-actual-sextic-exact-ray/governance-DIRECTION.snapshot.txt'
            rec=row(snapshot);assert rec['sha256']==h
            dependencies[rec['path']]=rec
            historical_policy.append({'observed_live_path':name,'observed_sha256':h,
                'immutable_snapshot_path':rec['path'],'mathematical_computations_depend_on_policy_bytes':False})
            continue
        rec=row(ROOT/name);assert rec['sha256']==h
        if name!='research-goal-20261017-actual-sextic-lean-plan/inventory.py':dependencies[name]=rec
    for rec in report['naive_selected_existing_API_import_closure']['files']:
        actual=row(ROOT/rec['path']);assert actual==rec;dependencies[rec['path']]=actual
    files=[row(p) for p in [HERE/'inventory.py',HERE/'static-inventory.json',HERE/'PLAN.zh.md',Path(__file__)]]
    result={'scope':__doc__,'files':files,'dependency_files':list(dependencies.values()),
        'historical_policy_observations':historical_policy,'live_direction_document_pinned':False,
        'static_active_dependency_and_source_inventory_passed':True,
        'exact_certificate_replayed_here':False,'dependency_transfer_payments_computed':False,
        'new_actual_kernel_evaluations':0,'optimizer_calls':0,'eigensolver_calls':0,'Lean_invocations':0,
        'actual_cell_exclusion_proven':False,'global_floor_proved':False,'website_single_file_compliance_proved':False,
        'new_zero_proportion_proven':False}
    target=HERE/'actual-lean-plan-files.json';raw=(json.dumps(result,indent=2,allow_nan=False)+'\n').encode()
    if target.exists():assert target.read_bytes()==raw,'Frozen pin differs; choose a new path.'
    else:target.write_bytes(raw)
    print(json.dumps({'pin':row(target),'report':row(HERE/'static-inventory.json'),
        'retained_files':len(files),'retained_bytes':sum(r['bytes'] for r in files)}))


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
