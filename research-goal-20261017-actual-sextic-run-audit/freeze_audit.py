"""Freeze one completed-run metadata/archive audit, without rerunning a solver."""
from pathlib import Path
import hashlib
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent


def row(p):
    raw=p.read_bytes()
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}


def main():
    receipt=json.loads((HERE/'independent-record-audit.json').read_bytes())
    assert receipt['source_sha256_start']==receipt['source_sha256_end']
    assert receipt['status']=='single_run_records_sources_monitor_and_native_archive_independently_passed'
    assert receipt['complete_native_lengths']==[5005,111144,111144]
    assert receipt['single_constructor_and_solve_recorded'] and receipt['guard_triggered'] is False
    assert receipt['exact_certificate_present'] is False
    assert receipt['solver_calls']==receipt['Lean_invocations']==receipt['dual_certificate_extractions']==0
    files=[row(p) for p in [HERE/'audit_record.py',HERE/'independent-record-audit.json',HERE/'README.md',Path(__file__)]]
    dependencies=[]
    for name,h in receipt['source_sha256_start'].items():
        rec=row(ROOT/name);assert rec['sha256']==h
        if name!='research-goal-20261017-actual-sextic-run-audit/audit_record.py':dependencies.append(rec)
    result={'scope':__doc__,'files':files,'dependency_files':dependencies,
        'independent_completed_run_record_audit_passed':True,'reported_infeasible_is_hint_only':True,
        'solver_calls':0,'Lean_invocations':0,'matrix_reconstructions':0,'eigensolver_calls':0,'dual_certificate_extractions':0,
        'exact_certificate_present':False,'exact_exclusion_proven':False,'global_floor_proved':False,'new_zero_proportion_proven':False}
    target=HERE/'run-audit-files.json';raw=(json.dumps(result,indent=2,allow_nan=False)+'\n').encode()
    if target.exists():assert target.read_bytes()==raw,'Frozen pin differs; choose a new path.'
    else:target.write_bytes(raw)
    print(json.dumps({'pin':row(target),'receipt':row(HERE/'independent-record-audit.json'),
        'retained_files':len(files),'retained_bytes':sum(r['bytes'] for r in files)}))


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
