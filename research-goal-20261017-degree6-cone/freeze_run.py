"""Freeze one inconclusive degree6 indirect run and its independent audit.

SCS installation files are runtime_dependency_files ONLY, never package
or repository dependency files to upload. Numerical hints are not proofs.
"""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
AUDIT=ROOT/'research-goal-20261017-degree6-run-audit';OUT=HERE/'degree6-cone-files.json'
def rec(p,name=None):return {'path':name or (p.relative_to(ROOT).as_posix() if p.is_relative_to(ROOT) else str(p)),
    'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
assert not OUT.exists();worker=json.loads((HERE/'worker-receipt.json').read_bytes());monitor=json.loads((HERE/'monitor.json').read_bytes())
assert worker['phase']=='completed_one_cold_CPU_indirect_SCS_attempt' and worker['SCS_invocations_started']==worker['SCS_solve_calls']==1
assert not worker['any_positive_hint'] and monitor['worker_processes_launched']==1 and monitor['SCS_solve_calls_recorded']==1
assert monitor['worker_exit_code']==0 and monitor['termination_reason'] is None
files=[p for p in HERE.iterdir() if p.is_file() and p!=OUT]+[p for p in AUDIT.iterdir() if p.is_file()]
names={p.relative_to(ROOT).as_posix() for p in files};deps={};runtime={}
for doc in [worker,monitor]:
    a=doc['input_sha256_start'];assert a==doc['input_sha256_end']
    for name,h in a.items():
        p=ROOT/name if not Path(name).is_absolute() else Path(name);r=rec(p,name);assert r['sha256']==h
        if name.startswith('tmp/') or not p.is_relative_to(ROOT):runtime[name]=r
        elif name not in names:deps[name]=r
am=json.loads((AUDIT/'audit-files.json').read_bytes())
for r in am.get('files',am.get('package_files',[])):assert rec(ROOT/r['path'])['sha256']==r['sha256']
hints=worker['full_hints'];assert rec(ROOT/hints['path'])['sha256']==hints['sha256'] and hints['lengths']==[5005,110963,110963]
assert all(p.stat().st_size<=4*1024**2 for p in files)
out={'scope':__doc__,'package_files':[rec(p) for p in sorted(files,key=lambda p:p.relative_to(ROOT).as_posix())],
    'dependency_files':[deps[k] for k in sorted(deps)],'runtime_dependency_files':[runtime[k] for k in sorted(runtime)],
    'runtime_version':worker['scs_version'],'runtime_API':'scs.SCS(linear_solver=scs.LinearSolver.CPU_INDIRECT).solve(warm_start=False)',
    'runtime_installation_not_to_be_staged':True,'one_actual_solver_call':True,'warm_start':False,
    'configured_time_limit_seconds':45,'actual_solver_seconds_including_setup_hint':worker['solver_seconds_including_setup_hint'],
    'hard45second_wall_limit_claimed':False,'iterations':worker['solver_info']['iter'],'solver_status':worker['solver_info']['status'],
    'monitor_peak_working_set_bytes':monitor['observed_peak_working_set_bytes'],'memory_threshold_bytes':1536*1024**2,
    'independent_record_audit_passed':True,'full_x_y_s_saved':True,'any_positive_hint':False,
    'exact_feasibility_or_infeasibility_proven':False,'new_actual_kernel_inputs':0,'Lean_invocations':0,
    'cell_exclusion_proven':False,'new_zero_proportion_proven':False}
OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
print(json.dumps({'manifest_sha256':rec(OUT)['sha256'],'package_files':len(files),'dependencies':len(deps),'runtime_only':len(runtime),'package_bytes':sum(p.stat().st_size for p in files)}))
