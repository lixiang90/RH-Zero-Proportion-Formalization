"""Freeze the completed actual-sextic aggregation preflight without rerunning it."""
from pathlib import Path
import hashlib
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent


def row(p):
    raw=p.read_bytes()
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}


def main():
    receipt=json.loads((HERE/'independent-preflight.json').read_bytes())
    assert receipt['source_sha256_start']==receipt['source_sha256_end']
    assert receipt['new_exact_canonical_rows_checked']==181
    assert receipt['exact_nonzero_coefficients_checked']==905724
    assert receipt['IEEE754_float64_values_checked_bitwise']==905905
    assert receipt['new_rows_energy_slack_column_absent'] and receipt['CSR_indices_and_indptr_exact']
    assert receipt['old_adapter_rows_checked']==5803 and receipt['box_scalar_rows']==8580
    dependencies=[]
    for name,h in receipt['source_sha256_start'].items():
        rec=row(ROOT/name);assert rec['sha256']==h
        if name!='research-goal-20261017-actual-sextic-cone-audit/preflight.py':dependencies.append(rec)
    files=[row(p) for p in [HERE/'preflight.py',HERE/'independent-preflight.json',HERE/'README.md',Path(__file__)]]
    result={'scope':__doc__,'files':files,'dependency_files':dependencies,
        'independent_exact_row_and_float_preflight_passed':True,
        'future_worker_settings_or_solver_run_audited':False,'pure_stdlib':True,
        'new_points_or_fits':0,'solver_calls':0,'Lean_invocations':0,
        'strict_feasibility_or_exclusion_claimed':False,'global_floor_proved':False,'new_zero_proportion_proven':False}
    target=HERE/'preflight-files.json';raw=(json.dumps(result,indent=2,allow_nan=False)+'\n').encode()
    if target.exists():assert target.read_bytes()==raw,'Frozen pin differs; choose a new path.'
    else:target.write_bytes(raw)
    print(json.dumps({'pin':row(target),'receipt':row(HERE/'independent-preflight.json'),
        'retained_files':len(files),'retained_bytes':sum(r['bytes'] for r in files)}))


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
