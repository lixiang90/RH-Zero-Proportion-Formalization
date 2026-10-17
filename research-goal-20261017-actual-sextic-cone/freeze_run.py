"""Pin the one bounded actual-sextic direct attempt and independent audits.

Native runtime files are runtime dependencies only. Reassembled large
arrays are reconstructed dependencies only, with lossless repository
pieces. This pin never asserts a new floor or exact solver certificate.
"""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
OUT=HERE/'actual-sextic-cone-files.json'
AUDITS=[ROOT/'research-goal-20261017-actual-sextic-cone-audit',ROOT/'research-goal-20261017-actual-sextic-run-audit']
def rec(p,name=None):
    return {'path':name or (p.relative_to(ROOT).as_posix() if p.is_relative_to(ROOT) else str(p)),
        'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
assert not OUT.exists()
worker=json.loads((HERE/'worker-receipt.json').read_bytes());monitor=json.loads((HERE/'monitor.json').read_bytes())
assert monitor['phase']=='single_worker_monitor_complete' and monitor['worker_processes_launched']==1
assert worker['SCS_invocations_started']<=1 and worker['SCS_solve_calls']<=1
assert monitor['solver_retries']==0 and monitor['total_worker_wall_limit_seconds']==90
for directory in AUDITS:assert directory.is_dir()
assert any(p.name.endswith('files.json') for p in AUDITS[1].iterdir())
reconstructed={}
restore=json.loads((HERE/'restore-inputs.json').read_bytes())
for row in restore['outputs']:
    p=HERE/row['name'];actual=rec(p);assert actual['bytes']==row['bytes'] and actual['sha256']==row['sha256']
    assert b''.join((HERE/r['name']).read_bytes() for r in row['parts'])==p.read_bytes()
    for r in row['parts']:assert rec(HERE/r['name'])['sha256']==r['sha256']
    reconstructed[actual['path']]=actual
hints=worker.get('full_hints')
if hints:
    p=ROOT/hints['path'];actual=rec(p);assert actual['bytes']==hints['bytes'] and actual['sha256']==hints['sha256']
    assert hints['lengths']==[5005,111144,111144]
    if p.stat().st_size>4*1024**2:
        pieces=hints['lossless_parts']
        assert b''.join((HERE/r['name']).read_bytes() for r in pieces)==p.read_bytes()
        for r in pieces:assert rec(HERE/r['name'])['sha256']==r['sha256']
        reconstructed[actual['path']]=actual
files=[p for p in HERE.iterdir() if p.is_file() and p!=OUT and p.relative_to(ROOT).as_posix() not in reconstructed]
files += [p for directory in AUDITS for p in directory.iterdir() if p.is_file()]
assert all(not p.name.endswith('.partial') and p.stat().st_size<=4*1024**2 for p in files)
names={p.relative_to(ROOT).as_posix() for p in files};deps={};runtime={}
docs=[worker,monitor,json.loads((HERE/'aggregation.json').read_bytes())]
for directory in AUDITS:
    docs += [json.loads(p.read_bytes()) for p in directory.iterdir() if p.suffix=='.json']
for doc in docs:
    for label in ['input_sha256','source_sha256']:
        if label+'_start' not in doc:continue
        start=doc[label+'_start'];assert start==doc[label+'_end']
        for name,h in start.items():
            p=Path(name) if Path(name).is_absolute() else ROOT/name;actual=rec(p,name);assert actual['sha256']==h
            if name.startswith('tmp/') or not p.is_relative_to(ROOT):runtime[name]=actual
            elif name in reconstructed:assert reconstructed[name]==actual
            elif name not in names:deps[name]=actual
    for label in ['files','package_files','dependency_files']:
        for actual in doc.get(label,[]):
            name=actual['path'];p=ROOT/name;checked=rec(p,name);assert checked['sha256']==actual['sha256'] and checked['bytes']==actual['bytes']
            if name.startswith('tmp/') or not p.is_relative_to(ROOT):runtime[name]=checked
            elif name in reconstructed:assert reconstructed[name]==checked
            elif name not in names:deps[name]=checked
assert not (set(deps)&set(runtime)) and not (set(deps)&set(reconstructed))
assert not (names&set(runtime)) and not (names&set(reconstructed))
out={'scope':__doc__,'package_files':[rec(p) for p in sorted(files,key=lambda p:p.relative_to(ROOT).as_posix())],
    'dependency_files':[deps[k] for k in sorted(deps)],'reconstructed_dependency_files':[reconstructed[k] for k in sorted(reconstructed)],
    'runtime_dependency_files':[runtime[k] for k in sorted(runtime)],'runtime_version':worker['scs_version'],
    'runtime_API':'scs.SCS(linear_solver=scs.LinearSolver.QDLDL).solve(warm_start=False)',
    'runtime_installation_not_to_be_staged':True,'reconstructed_originals_not_to_be_staged':True,
    'single_worker_process':True,'SCS_initializations_started':worker['SCS_invocations_started'],'SCS_solve_calls':worker['SCS_solve_calls'],
    'solver_retries':0,'warm_start':False,'configured_time_limit_seconds':45,'parent_total_worker_wall_limit_seconds':90,
    'maximum_iterations':2000,'eps_abs':1e-7,'eps_rel':1e-7,'BLAS_threads':1,
    'actual_solver_seconds_including_setup_hint':worker.get('solver_seconds_including_setup_hint'),
    'monitor_peak_working_set_bytes':monitor.get('observed_peak_working_set_bytes'),
    'memory_threshold_bytes':1536*1024**2,'termination_reason':monitor.get('termination_reason'),
    'solver_status':worker.get('solver_info',{}).get('status'),'iterations':worker.get('solver_info',{}).get('iter'),
    'independent_exact_181row_preflight_passed':True,'independent_wrapper_and_completed_record_audits_passed':True,
    'full_native_x_y_s_saved':bool(hints),'any_positive_numerical_hint':worker.get('any_positive_hint'),
    'exact_feasibility_or_infeasibility_proven':False,'new_actual_kernel_inputs':0,'Lean_invocations':0,
    'actual_analytic_instances_Lean_proved':False,'cell_exclusion_proven':False,'new_zero_proportion_proven':False}
OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
print(json.dumps({'manifest_sha256':rec(OUT)['sha256'],'package_files':len(files),'dependencies':len(deps),
    'reconstructed_only':len(reconstructed),'runtime_only':len(runtime),'package_bytes':sum(p.stat().st_size for p in files)}))
