"""Freeze the completed fixed degree6 preparation and failed retained-Gram budget."""
from pathlib import Path
import hashlib
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent


def row(p):
    raw=p.read_bytes()
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}


def main():
    preparation=json.loads((HERE/'preparation.json').read_bytes())
    budget=json.loads((HERE/'budget.json').read_bytes())
    assert preparation['source_sha256_start']==preparation['source_sha256_end']
    assert budget['source_sha256_start']==budget['source_sha256_end']
    assert preparation['Gram_payment_K_evaluated'] is False
    assert budget['status']=='fixed_retained_Gram_edge6_transfer_budget_FAIL'
    assert budget['strict_budget_passed'] is False
    assert budget['K_arithmetic_evaluations_including_failed_serialization']==2
    assert budget['fixed_mathematical_candidates']==1
    own=['prepare.py','preparation.json','packet.json.gz','evaluate_initial_serialization_failure.py',
         'evaluate_once.py','budget.json','serialization-recovery.txt','README.zh.md','freeze.py']
    files=[row(HERE/name) for name in own];ownpaths={r['path'] for r in files};dependencies={}
    for receipt in [preparation,budget]:
        for name,h in receipt['source_sha256_start'].items():
            entry=row(ROOT/name);assert entry['sha256']==h
            if name not in ownpaths:dependencies[name]=entry
    epsilon=ROOT/'research-goal-20261017-edge6-transfer-audit/independent-replay.json'
    assert epsilon.exists();dependencies[epsilon.relative_to(ROOT).as_posix()]=row(epsilon)
    result={'scope':__doc__,'files':files,'dependency_files':list(dependencies.values()),
        'Bernstein_degree':6,'subdivisions_per_edge':1,'all_shared5005_identity_checks_passed':True,
        'independent_epsilon_replay_receipt':row(epsilon),'total_K_budget_passed':False,
        'fixed_mathematical_candidates':1,'arithmetic_executions_including_serialization_failure':2,
        'actual_old_analytic_dependencies_removed':False,'eight_swap_actual_dependencies_preserved':True,
        'no_new_frontier_or_ancestor_closure_claimed':True,'cell_historically_closed_scope':True,
        'solver_calls':0,'eigensolver_calls':0,'Lean_invocations':0,'new_points':0,
        'further_bound_or_parameter_scans':0,'actual_cell_exclusion_proven':False,
        'global_cover_proven':False,'website_source_compliance_proven':False,'new_zero_proportion_proven':False}
    target=HERE/'edge6-transfer-files.json';raw=(json.dumps(result,indent=2,allow_nan=False)+'\n').encode()
    if target.exists():assert target.read_bytes()==raw,'Frozen manifest differs; choose a new path.'
    else:target.write_bytes(raw)
    print(json.dumps({'pin':row(target),'budget':row(HERE/'budget.json'),
        'retained_files':len(files),'retained_bytes':sum(r['bytes'] for r in files)}))


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
