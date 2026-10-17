"""Freeze the completed independent stationary-swap audit without rerunning it."""
from pathlib import Path
import hashlib,json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent


def row(p):
    b=p.read_bytes()
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}


def main():
    receipt=json.loads((HERE/'independent-replay.json').read_bytes())
    assert receipt['input_sha256_start']==receipt['input_sha256_end']
    deps=[]
    for name,h in receipt['input_sha256_start'].items():
        item=row(ROOT/name);assert item['sha256']==h;deps.append(item)
    assert receipt['upper_is_strictly_positive'] and not receipt['latest_exact714_separated']
    assert receipt['anchor_derivative_intervals_orders_2_to_6_rebuilt']==40
    assert receipt['distinct_q7_degree16_cells_rebuilt']==391
    assert receipt['weighted_power_integrals_independently_integrated_and_formula_checked']==40
    assert not receipt['producer_or_helper_imported'] and receipt['solver_calls']==receipt['Lean_invocations']==0
    files=[row(p) for p in [HERE/'independent_stationary_replay.py',HERE/'independent-replay.json',HERE/'README.md',Path(__file__)]]
    out={'scope':__doc__,'files':files,'dependency_files':deps,
         'independent_exact_arithmetic_replay_passed':True,'strict_separation_found':False,
         'producer_or_helper_imported':False,'new_points':0,'new_function_samples':0,
         'solver_calls':0,'Lean_invocations':0,'new_actual_analytic_obligations_discharged':False,
         'new_cell_exclusion':False,'new_zero_proportion_proven':False}
    p=HERE/'stationary-audit-files.json';raw=(json.dumps(out,indent=2,allow_nan=False)+'\n').encode()
    if p.exists():assert p.read_bytes()==raw,'Frozen pin differs; use a new path.'
    else:p.write_bytes(raw)
    print(json.dumps({'pin':row(p),'receipt':row(HERE/'independent-replay.json'),'files':len(files),'bytes':sum(x['bytes'] for x in files)}))


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
