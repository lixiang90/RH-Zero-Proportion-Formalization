"""Freeze the additive source gate; do not rerun a worker or alter the preflight pin."""
from pathlib import Path
import hashlib
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent


def row(p):
    raw=p.read_bytes()
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}


def main():
    receipt=json.loads((HERE/'worker-source-review.json').read_bytes())
    assert receipt['source_sha256_start']==receipt['source_sha256_end']
    assert receipt['status']=='frozen_worker_static_gate_passed_for_one_cold_CPU_direct_attempt'
    assert receipt['matrix_shape']==[111144,5005] and receipt['exact_nonzero_count']==3153411
    assert receipt['worker_executions']==receipt['solver_calls']==receipt['Lean_invocations']==0
    files=[row(p) for p in [HERE/'review_worker.py',HERE/'worker-source-review.json',HERE/'WORKER_REVIEW.md',Path(__file__)]]
    dependencies=[]
    for name,h in receipt['source_sha256_start'].items():
        rec=row(ROOT/name);assert rec['sha256']==h
        if name!='research-goal-20261017-actual-sextic-cone-audit/review_worker.py':dependencies.append(rec)
    result={'scope':__doc__,'files':files,'dependency_files':dependencies,
        'source_only_worker_gate_passed':True,'worker_executions':0,'solver_calls':0,'Lean_invocations':0,
        'authorized_future_attempt_count':1,'runtime_completed':False,
        'numeric_or_exact_exclusion_claimed':False,'global_floor_proved':False,'new_zero_proportion_proven':False}
    p=HERE/'worker-review-files.json';raw=(json.dumps(result,indent=2,allow_nan=False)+'\n').encode()
    if p.exists():assert p.read_bytes()==raw,'Frozen pin differs; choose a new path.'
    else:p.write_bytes(raw)
    print(json.dumps({'pin':row(p),'receipt':row(HERE/'worker-source-review.json'),
        'retained_files':len(files),'retained_bytes':sum(r['bytes'] for r in files)}))


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
