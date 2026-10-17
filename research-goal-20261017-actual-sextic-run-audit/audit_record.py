"""One independent read-only audit of the completed single SCS run record.

Check frozen sources, configuration, monitor, complete native x/y/s archive
hashes and lengths, and explicit nonfinite-string encoding. No solver,
matrix reconstruction, eigensolver, dual extraction, fit or Lean process.
The reported infeasibility residual remains a numerical hint only.
Default read-only; --write-receipt creates an absent immutable receipt.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import math
import sys
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
CONE=ROOT/'research-goal-20261017-actual-sextic-cone'
PRE=ROOT/'research-goal-20261017-actual-sextic-cone-audit'
OUT=HERE/'independent-record-audit.json'
PINS={'worker-receipt.json':'36968605fc86c346500baaed901e472f9e17e4163d466b1a1479495dff1783be',
      'monitor.json':'3a1fdadabd3b9fac4d0ff9b0a222efb02a6bcbafe3aa3aa18415b41e54fa9203',
      'actual-sextic-hints.json.gz':'9ad1f4594b3981f2a5bff6e1ffbd1d76ae1e24d5f8b3538b7e89846d8b4ba693',
      'worker.py':'c0c9c942eae956576934ca9bd8b60aa3146077f062f80e1bed672fffc1e59626',
      'run_once.py':'df7b67869457d4c523b81f047447b36dda025ceae1747a27e604662280499cc5'}


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def reject_constant(name):raise ValueError('Unquoted nonfinite JSON token: '+name)


def read(p):return json.loads(p.read_bytes(),parse_constant=reject_constant)


def values_policy(values):
    counts={'finite':0,'NaN':0,'Infinity':0,'-Infinity':0}
    for x in values:
        if isinstance(x,str):assert x in counts and x!='finite';counts[x]+=1
        else:
            assert not isinstance(x,bool) and isinstance(x,(int,float)) and math.isfinite(x)
            counts['finite']+=1
    assert sum(counts.values())==len(values)
    return counts


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic()
    paths=[Path(__file__)]+[CONE/name for name in PINS]+[CONE/'worker-stdout.log',CONE/'worker-stderr.log',
        PRE/'worker-source-review.json',PRE/'worker-review-files.json',PRE/'independent-preflight.json',PRE/'preflight-files.json']
    for name,h in PINS.items():assert sha(CONE/name)==h
    worker=read(CONE/'worker-receipt.json');monitor=read(CONE/'monitor.json')
    assert worker['input_sha256_start']==worker['input_sha256_end'] and worker['all_inputs_unchanged']
    assert monitor['input_sha256_start']==monitor['input_sha256_end'] and monitor['all_inputs_unchanged']
    for record in [worker,monitor]:
        for name,h in record['input_sha256_start'].items():
            p=ROOT/name;assert sha(p)==h
            if p not in paths:paths.append(p)
    initial={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    source_review=read(PRE/'worker-source-review.json')
    assert source_review['status']=='frozen_worker_static_gate_passed_for_one_cold_CPU_direct_attempt'
    for name,h in source_review['source_sha256_start'].items():assert sha(ROOT/name)==h
    assert source_review['source_sha256_start']==source_review['source_sha256_end']
    preflight=read(PRE/'independent-preflight.json')
    assert preflight['status']=='all181_exact_rows_old_adapter_and_every_CSR_float_independently_passed'
    for name,h in preflight['source_sha256_start'].items():assert sha(ROOT/name)==h
    assert preflight['source_sha256_start']==preflight['source_sha256_end']
    for name in ['preflight-files.json','worker-review-files.json']:
        pin=read(PRE/name)
        for entry in pin['files']+pin['dependency_files']:
            p=ROOT/entry['path'];assert p.stat().st_size==entry['bytes'] and sha(p)==entry['sha256']

    assert worker['phase']=='completed_one_cold_CPU_direct_actual_sextic_SCS_attempt'
    assert monitor['phase']=='single_worker_monitor_complete' and monitor['worker_exit_code']==0
    assert worker['PID']==monitor['PID'] and worker['PID']>0
    assert monitor['worker_processes_launched']==1 and monitor['solver_retries']==0
    assert worker['SCS_invocations_started']==worker['SCS_solve_calls']==monitor['SCS_solve_calls_recorded']==1
    assert monitor['worker_receipt_sha256']==PINS['worker-receipt.json']
    assert monitor['worker_final_phase']==worker['phase']
    assert monitor['termination_reason'] is None and monitor['terminated_only_worker_PID'] is None
    assert 'monitor_exception' not in monitor and 'exception' not in worker
    assert monitor['memory_limit_bytes']==worker['memory_limit_bytes']==1536*1024**2
    assert monitor['total_worker_wall_limit_seconds']==90
    assert worker['elapsed_milliseconds']<=monitor['elapsed_milliseconds']<90000
    assert monitor['elapsed_milliseconds']==68198
    snapshots=monitor['snapshots'];assert snapshots
    assert [s['elapsed_milliseconds'] for s in snapshots]==sorted(s['elapsed_milliseconds'] for s in snapshots)
    peak=max(s['peak_working_set_bytes'] for s in snapshots)
    assert peak==monitor['observed_peak_working_set_bytes']==728928256
    assert max(max(s['working_set_bytes'],s['peak_working_set_bytes']) for s in snapshots)<monitor['memory_limit_bytes']
    phases=[s['phase'] for s in worker['memory_snapshots']]
    assert phases.index('one_CPU_direct_SCS_initialization_starting')<phases.index('one_cold_CPU_direct_SCS_solve_running')
    assert phases.index('one_cold_CPU_direct_SCS_solve_running')<phases.index('native_full_x_y_s_saved_before_diagnostics')<phases.index(worker['phase'])
    assert all(s['peak_working_set_bytes']<worker['memory_limit_bytes'] for s in worker['memory_snapshots'])
    expected={'linear_solver':'cpu_direct_QDLDL','time_limit_seconds':45,'maximum_iterations':2000,
        'eps_abs':1e-7,'eps_rel':1e-7,'cold_solve':True,'warm_start':False,'BLAS_threads':1,
        'matrix_shape':[111144,5005],'matrix_nonzero_count':3153411,'linear_rows':14564,
        'old_scalar_rows_retained':14383,'new_unsoftened_actual_sextic_rows':181,'PSD_blocks':73,'PSD_lower_triangle_entries':96580}
    for key,value in expected.items():assert worker[key]==value
    assert worker['scs_version']=='3.3.1'
    assert worker['full_model_no_constraints_dropped'] and worker['all_new_rows_have_no_energy_slack']
    assert worker['independent_exact_newrow_aggregation_preflight_passed']
    assert worker['rank1_PSD_or_model_feasibility_asserted'] is False
    info=worker['solver_info']
    assert info['status']=='infeasible' and info['status_val']==-2 and info['iter']==125
    assert info['lin_sys_solver']=='sparse-direct-amd-qdldl'
    assert info['res_infeas']==4.130910915064931e-12
    assert 0<info['solve_time']/1000<45
    assert 0<worker['solver_seconds_including_setup_hint']<90

    hint_record=worker['full_hints'];hint_path=ROOT/hint_record['path']
    compressed=hint_path.read_bytes();raw=gzip.decompress(compressed)
    assert len(compressed)==hint_record['bytes']==1057101
    assert hashlib.sha256(compressed).hexdigest()==hint_record['sha256']==PINS['actual-sextic-hints.json.gz']
    assert len(raw)==hint_record['uncompressed_bytes']==3187403
    assert hashlib.sha256(raw).hexdigest()==hint_record['uncompressed_sha256']=='4012d1fb4e02558bb45b28b5316490fd1ab197e1c44a6a60ee497b32835550f3'
    native=json.loads(raw,parse_constant=reject_constant)
    assert native['source_receipt']=='worker-receipt.json'
    arrays=[native['raw_primal_hint'],native['raw_dual_hint'],native['raw_conic_slack_hint']]
    assert [len(a) for a in arrays]==hint_record['lengths']==[5005,111144,111144]
    policies=[values_policy(a) for a in arrays]
    assert policies[1]['finite']==111144
    assert policies[0]['NaN']==5005 and policies[2]['NaN']==111144
    assert all(p['Infinity']==p['-Infinity']==0 for p in policies)
    stdout=(CONE/'worker-stdout.log').read_text(encoding='utf8').splitlines()
    assert len(stdout)==1
    printed=json.loads(stdout[0],parse_constant=reject_constant)
    assert printed['phase']==worker['phase'] and printed['solver_info']==info
    assert (CONE/'worker-stderr.log').stat().st_size==0
    assert worker['any_positive_hint'] and worker['infeasible_dual_ray_hint']
    assert worker['actual_certificate'] is None
    for record in [worker,monitor]:
        assert record['Lean_invocations']==0 and record['cell_exclusion_proven'] is False and record['new_zero_proportion_proven'] is False
    assert worker['actual_analytic_instances_Lean_proved'] is False
    assert not any(name.split('.')[0] in ['numpy','scipy','scs'] for name in sys.modules)
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==initial
    report={'scope':__doc__,'status':'single_run_records_sources_monitor_and_native_archive_independently_passed',
        'source_sha256_start':initial,'source_sha256_end':final,'all_record_and_input_hashes_unchanged':True,
        'worker_PID':worker['PID'],'single_constructor_and_solve_recorded':True,
        'worker_exit_code':0,'guard_triggered':False,'reported_parent_wall_milliseconds':monitor['elapsed_milliseconds'],
        'observed_peak_working_set_bytes':peak,'reported_solver_status':info['status'],'reported_iterations':info['iter'],
        'reported_res_infeas_hint':info['res_infeas'],'reported_setup_plus_solve_seconds_hint':worker['solver_seconds_including_setup_hint'],
        'config_matches_frozen_source_gate':True,'complete_native_lengths':[len(a) for a in arrays],
        'native_array_finite_encoding_counts':dict(zip(['primal','dual','conic_slack'],policies)),
        'native_compressed_and_uncompressed_hashes_checked':True,'unquoted_nonfinite_JSON_rejected':True,
        'durable_before_diagnostics_source_order_and_phase_records_agree':True,
        'pure_stdlib':True,'producer_or_solver_imported':False,'matrix_reconstructions':0,'eigensolver_calls':0,
        'dual_certificate_extractions':0,'solver_calls':0,'Lean_invocations':0,'new_points_or_fits':0,
        'actual_analytic_instances_Lean_proved':False,'exact_certificate_present':False,
        'exact_exclusion_proven':False,'global_floor_proved':False,'new_zero_proportion_proven':False,
        'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    if args.write_receipt:OUT.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:report[k] for k in ['status','reported_solver_status','reported_iterations',
        'complete_native_lengths','observed_peak_working_set_bytes','elapsed_milliseconds']}))


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
