"""Freeze the completed independent actual-sextic STATIC replay; do not rerun it."""
from pathlib import Path
import hashlib
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent


def row(p):
    raw=p.read_bytes()
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}


def main():
    receipt=json.loads((HERE/'independent-replay.json').read_bytes())
    assert receipt['source_sha256_start']==receipt['source_sha256_end']
    assert receipt['point_derivative_intervals_checked']==287
    assert receipt['whole_grid_q7_degree16_cells_checked']==658
    assert receipt['span_power_coefficient_terms_checked']==41794
    assert receipt['shift_plans_checked']==2501 and receipt['shift_target_references_checked']==206278
    assert receipt['target_stream_fully_consumed'] and receipt['all_plans_used_by_rows']
    assert receipt['only_P5_multiplied_by_test_not_E6']
    dependencies=[]
    for name,h in receipt['source_sha256_start'].items():
        rec=row(ROOT/name);assert rec['sha256']==h
        if name!='research-goal-20261017-actual-sextic-audit/independent_replay.py':dependencies.append(rec)
    files=[row(p) for p in [HERE/'independent_replay.py',HERE/'independent-replay.json',HERE/'README.md',Path(__file__)]]
    result={'scope':__doc__,'files':files,'dependency_files':dependencies,
        'independent_exact_STATIC_replay_passed':True,'producer_imported':False,
        'new_points_or_moment_evaluations':0,'solver_calls':0,'Lean_invocations':0,
        'concrete_analytic_Lean_instances_proved':False,'old_exact714_extension_decided':False,
        'strict_projection_shrink_proved':False,'cell_exclusion_proven':False,'new_zero_proportion_proven':False}
    target=HERE/'sextic-audit-files.json';raw=(json.dumps(result,indent=2,allow_nan=False)+'\n').encode()
    if target.exists():assert target.read_bytes()==raw,'Frozen pin differs; choose a new path.'
    else:target.write_bytes(raw)
    print(json.dumps({'pin':row(target),'receipt':row(HERE/'independent-replay.json'),
        'retained_files':len(files),'retained_bytes':sum(r['bytes'] for r in files)}))


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
