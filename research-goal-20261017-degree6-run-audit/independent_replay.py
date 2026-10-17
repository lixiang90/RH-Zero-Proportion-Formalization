"""Independent stdlib audit of the completed single degree6 numerical run.

Read source/receipts/monitor/hint payload only. Check hashes, configuration,
layout metadata, one monitored PID/call count, shapes and finite hints.
No solver import/call, matrix reconstruction, eigenvalue recomputation,
new point or exact feasibility test. Default read-only; --write-receipt
creates an absent receipt once.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse, ast, gzip, hashlib, json, math, time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;FOLDER=ROOT/'research-goal-20261017-degree6-cone';OUT=HERE/'independent-replay.json'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic();wp=FOLDER/'worker-receipt.json';mp=FOLDER/'monitor.json';p=json.loads(wp.read_bytes());m=json.loads(mp.read_bytes())
    assert digest(wp)=='fc2bbd30b85ff140a4ce61bbd06d2dd4fe3cd1410dff703440ec62e04aaa276e'
    inputs={**p['input_sha256_start'],**m['input_sha256_start'],wp.relative_to(ROOT).as_posix():digest(wp),
        mp.relative_to(ROOT).as_posix():digest(mp),Path(__file__).relative_to(ROOT).as_posix():digest(Path(__file__))}
    assert p['input_sha256_start']==p['input_sha256_end']and p['all_inputs_unchanged']
    assert m['input_sha256_start']==m['input_sha256_end']and m['all_inputs_unchanged']
    for name,h in inputs.items():assert digest(ROOT/name)==h,('changed input',name)
    src=(FOLDER/'worker.py').read_text();parent=(FOLDER/'run_once.py').read_text();tree=ast.parse(src);ptree=ast.parse(parent)
    calls=[n for n in ast.walk(tree)if isinstance(n,ast.Call)]
    constructors=[n for n in calls if isinstance(n.func,ast.Attribute)and isinstance(n.func.value,ast.Name)and n.func.value.id=='scs'and n.func.attr=='SCS']
    solves=[n for n in calls if isinstance(n.func,ast.Attribute)and isinstance(n.func.value,ast.Name)and n.func.value.id=='engine'and n.func.attr=='solve']
    assert len(constructors)==len(solves)==1
    kw={v.arg:ast.unparse(v.value)for v in constructors[0].keywords}
    assert kw=={'linear_solver':'scs.LinearSolver.CPU_INDIRECT','verbose':'False','time_limit_secs':'45','max_iters':'1000','eps_abs':'1e-06','eps_rel':'1e-06'}
    assert {v.arg:ast.unparse(v.value)for v in solves[0].keywords}=={'warm_start':'False'}
    assert 'np.linalg.norm(A.T@dual+c,np.inf)'in src and 'np.linalg.norm(A.T@dual-c,np.inf)'not in src
    assert 'col=SLACK if col==714 else col'in src and 'factor=1. if i==j else np.sqrt(2)'in src
    assert "divisor=max([F(1)]+[abs(a) for a in coeff])"in src and 'bb[rowid]=a'in src and 'vv[used]=-a'in src
    pcalls=[n for n in ast.walk(ptree)if isinstance(n,ast.Call)]
    popen=[n for n in pcalls if isinstance(n.func,ast.Attribute)and isinstance(n.func.value,ast.Name)and n.func.value.id=='subprocess'and n.func.attr=='Popen']
    assert len(popen)==1 and "max(q.WorkingSetSize,q.PeakWorkingSetSize)>LIMIT"in parent
    assert 'process.terminate()'in parent and 'taskkill'not in parent and 'TerminateProcess'not in parent
    assert 'SLACK=5004'in src and 'SCALAR=14383;N=5005'in src
    build=json.loads((ROOT/'research-goal-20261017-degree6-static/degree6-build.json').read_bytes())
    gate=json.loads((ROOT/'research-goal-20261017-degree6-audit/independent-replay.json').read_bytes())
    assert gate['status']=='complete_factored_degree6_representation_independently_decoded'and gate['all_inputs_unchanged']
    assert gate['total_scalar_rows']==build['total_scalar_rows']==p['linear_rows']==14383
    assert p['optimization_variables']==build['optimization_variables_including_slack']==5005
    assert p['energy_slack_column']==build['slack_column']==5004 and build['old_slack_column_remap']==[714,5004]
    assert p['PSD_blocks']==build['PSD_blocks']==73 and p['PSD_lower_triangle_entries']==build['PSD_lower_triangle_entries']==96580
    assert build['PSD_sizes']==[220]+[55]*46+[10]*26
    assert sum(n*(n+1)//2 for n in build['PSD_sizes'])==96580
    assert p['matrix_shape']==[110963,5005]and p['matrix_nonzero_count']==2247687
    assert p['exact_rank1_term_identities_checked']==1416525 and p['full_model_no_constraints_dropped']
    assert len(p['positive_rational_uniform_PSD_divisors'])==73 and all(F(v)>0 for v in p['positive_rational_uniform_PSD_divisors'])
    assert p['PID']==m['PID']==20232 and m['worker_processes_launched']==p['SCS_invocations_started']==p['SCS_solve_calls']==m['SCS_solve_calls_recorded']==1
    assert m['worker_exit_code']==0 and m['worker_final_phase']==p['phase']=='completed_one_cold_CPU_indirect_SCS_attempt'
    assert m['phase']=='single_worker_monitor_complete'and m['worker_receipt_sha256']==digest(wp)
    assert m['solver_retries']==0 and m['terminated_only_worker_PID']is None and m['termination_reason']is None
    assert p['cold_solve']and not p['warm_start']and p['BLAS_threads']==1 and p['linear_solver']=='cpu_indirect'
    assert p['time_limit_seconds']==45 and p['maximum_iterations']==1000 and p['eps_abs']==p['eps_rel']==1e-6
    assert p['memory_limit_bytes']==m['memory_limit_bytes']==1536*1024**2
    assert all(s['working_set_bytes']>0 and s['peak_working_set_bytes']>=s['working_set_bytes']for s in m['snapshots'])
    assert all(a['elapsed_milliseconds']<b['elapsed_milliseconds']for a,b in zip(m['snapshots'],m['snapshots'][1:]))
    peak=max(s['peak_working_set_bytes']for s in m['snapshots']);assert peak==m['observed_peak_working_set_bytes']==391667712<1536*1024**2
    h=p['full_hints'];hp=ROOT/h['path'];assert digest(hp)==h['sha256']=='fdd36a5ceb9bdcd9088d00e306d86ffa92a799eeeab58114ec75221b859a0791'
    assert hp.stat().st_size==h['bytes']==1967899;raw=gzip.decompress(hp.read_bytes())
    assert len(raw)==h['uncompressed_bytes']==4589310 and hashlib.sha256(raw).hexdigest()==h['uncompressed_sha256']
    hint=json.loads(raw);vectors=[hint['raw_primal_hint'],hint['raw_dual_hint'],hint['raw_conic_slack_hint']]
    assert list(map(len,vectors))==h['lengths']==[5005,110963,110963]
    assert all(isinstance(v,(int,float))and not isinstance(v,bool)and math.isfinite(v)for vector in vectors for v in vector)
    inputs[hp.relative_to(ROOT).as_posix()]=digest(hp)
    info=p['solver_info'];assert info['iter']==225 and info['status_val']==2 and info['status']=='solved (inaccurate - reached time_limit_secs)'
    assert p['solver_seconds_including_setup_hint']>45 and info['solve_time']/1000>45
    assert abs(info['res_pri']-p['packed_primal_residual_infinity_hint'])<1e-12
    assert abs(info['res_dual']-p['dual_stationarity_infinity_hint'])<1e-12
    assert p['raw_energy_slack_hint']==vectors[0][5004]*.001<0
    assert len(p['PSD_minimum_eigenvalues_hint'])==73 and min(p['PSD_minimum_eigenvalues_hint'])==p['minimum_normalized_PSD_eigenvalue_hint']<0
    assert not p['any_positive_hint']and not p['infeasible_dual_ray_hint']and not p['positive_energy_slack_hint']
    for name,hsh in inputs.items():assert digest(ROOT/name)==hsh
    result={'scope':__doc__,'passed':True,'source_sha256_start':inputs,'source_sha256_end':inputs,'all_inputs_unchanged':True,
        'original_worker_sha256':digest(FOLDER/'worker.py'),'original_monitor_source_sha256':digest(FOLDER/'run_once.py'),
        'single_worker_PID':20232,'worker_launches':1,'solver_constructions_in_source':1,'solver_solve_calls_recorded':1,
        'dual_stationarity_diagnostic_corrected_to_Atranspose_y_plus_c':True,
        'scalar_rows':14383,'PSD_blocks':73,'PSD_entries':96580,'variables':5005,'slack_column':5004,'old_slack_column':714,
        'positive_uniform_rational_PSD_divisors_checked':73,'matrix_reassembled':False,'fixed_rank1_identity_reexecuted':False,
        'configured_time_limit_seconds':45,'actual_solver_seconds_including_setup':p['solver_seconds_including_setup_hint'],
        'actual_internal_solve_seconds':info['solve_time']/1000,'configured_time_limit_is_not_a_hard_wall_clock_limit':True,
        'time_limit_interpretation':'The returned internal-time-limit status arrived after51.87 wall seconds including setup; solver-internal stopping checks are not a hard45-second kill.',
        'reported_iterations':225,'reported_status':info['status'],'reported_primal_residual':info['res_pri'],'reported_dual_residual':info['res_dual'],
        'reported_minimum_PSD_eigenvalue_hint':p['minimum_normalized_PSD_eigenvalue_hint'],'eigenvalues_recomputed':False,
        'peak_working_set_bytes_observed':peak,'memory_limit_bytes':1536*1024**2,'memory_guard_triggered':False,
        'hints_compressed_sha256':digest(hp),'hint_lengths':list(map(len,vectors)),'all_hints_finite':True,
        'any_positive_or_infeasible_hint':False,'numerical_primal_is_not_an_exact_feasible_point':True,
        'solver_imports':0,'solver_calls':0,'eigh_calls':0,'new_points':0,'Lean_invocations':0,
        'exact_feasibility_or_infeasibility_proven':False,'cell_exclusion_proven':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-began}
    if args.write_receipt:OUT.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'passed':True,'worker_PID':20232,'solver_calls':1,'actual_solver_wall_seconds':p['solver_seconds_including_setup_hint'],
        'all_hints_finite':True,'hint_lengths':list(map(len,vectors)),'any_positive_hint':False,
        'receipt_sha256':digest(OUT)if args.write_receipt else None,'seconds':result['seconds']}),flush=True)
if __name__=='__main__':
    assert __debug__
    main()
