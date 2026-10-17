"""Read-only static source gate for the ONE actual-sextic CPU-direct attempt.

Parse source without importing the worker, NumPy, SciPy or SCS. Check the
one-call cold direct configuration and own-PID monitor, and independently
count all retained scalar/PSD rows and nonzeros. No worker is executed.
--write-receipt creates an absent additive receipt; old preflight is frozen.
"""
from pathlib import Path
from array import array
import argparse
import ast
import gzip
import hashlib
import json
import sys
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
CONE=ROOT/'research-goal-20261017-actual-sextic-cone'
STATIC=ROOT/'research-goal-20261017-degree6-static'
OUT=HERE/'worker-source-review.json'
PINS={'worker.py':'c0c9c942eae956576934ca9bd8b60aa3146077f062f80e1bed672fffc1e59626',
      'run_once.py':'df7b67869457d4c523b81f047447b36dda025ceae1747a27e604662280499cc5'}


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def gzjson(p):return json.loads(gzip.decompress(p.read_bytes()))


def literal_keywords(call):
    out={}
    for keyword in call.keywords:
        if isinstance(keyword.value,ast.Constant):out[keyword.arg]=keyword.value.value
        else:out[keyword.arg]=ast.unparse(keyword.value)
    return out


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic()
    paths=[Path(__file__),CONE/'worker.py',CONE/'run_once.py',HERE/'independent-preflight.json',
        HERE/'preflight-files.json',STATIC/'degree6-model.json.gz',STATIC/'degree6-targets.bin',
        STATIC/'degree6-entryplans.bin',CONE/'aggregation.json',CONE/'new-row-hashes.json',
        ROOT/'tmp/goal-20261016/python-sdp/scs/_scs_direct.cp314-win_amd64.pyd']
    for name,h in PINS.items():assert sha(CONE/name)==h
    model=gzjson(paths[5]);oldpaths=[ROOT/name for name in model['old_row_adapter']['sources']]
    paths.extend(oldpaths)
    initial={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    assert initial[paths[10].relative_to(ROOT).as_posix()]=='55583ea77840727ee357ba7b42c5443caf250f55039199a924a2b1910459cd6c'
    source=(CONE/'worker.py').read_text(encoding='utf8');monitor=(CONE/'run_once.py').read_text(encoding='utf8')
    worker_ast=ast.parse(source);monitor_ast=ast.parse(monitor)
    calls=[node for node in ast.walk(worker_ast) if isinstance(node,ast.Call)]
    constructors=[node for node in calls if ast.unparse(node.func)=='scs.SCS']
    solves=[node for node in calls if ast.unparse(node.func)=='engine.solve']
    assert len(constructors)==len(solves)==1
    config=literal_keywords(constructors[0]);solve_config=literal_keywords(solves[0])
    assert config=={'linear_solver':'scs.LinearSolver.QDLDL','verbose':False,'time_limit_secs':45,
                    'max_iters':2000,'eps_abs':1e-7,'eps_rel':1e-7}
    assert solve_config=={'warm_start':False}
    assert ast.unparse(constructors[0].args[1])=="{'l': SCALAR, 's': [b['size'] for b in model['blocks']]}"
    assert not any(isinstance(node,ast.Call) and ast.unparse(node.func) in ['eval','exec','os.system','subprocess.Popen','subprocess.run'] for node in ast.walk(worker_ast))
    assert len([node for node in ast.walk(monitor_ast) if isinstance(node,ast.Call) and ast.unparse(node.func)=='subprocess.Popen'])==1
    assert not any(isinstance(node,ast.Call) and ast.unparse(node.func) in ['os.kill','os.system','subprocess.run'] for node in ast.walk(monitor_ast))
    assert source.index("os.environ[key]='1'")<source.index('import numpy as np')
    assert "['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']" in source
    assert "for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:env[k]='1'" in monitor
    for fragment in ["newgate['status']=='all181_exact_rows_old_adapter_and_every_CSR_float_independently_passed'",
        "newgate['source_sha256_start']==newgate['source_sha256_end']",
        "for name,h in newgate['source_sha256_start'].items():assert sha(ROOT/name)==h",
        "np.all(new_indices<SLACK)","assert rowid==14383","for r in range(181):",
        "col=SLACK if col==714 else col",'assert count==5004',
        "assert rowid==len(bb)==111144 and used==EXPECTED_NNZ",'assert A.nnz==EXPECTED_NNZ',
        'factor=1. if i==j else np.sqrt(2)','vv[used]=-a',
        'engine.solve(warm_start=False)','c[SLACK]=1.']:
        assert fragment in source
    native_position=source.index("x=result['x'];dual=result['y'];slack=result['s']")
    write_position=source.index('stream.write(compressed);stream.flush();os.fsync(stream.fileno())')
    replace_position=source.index('temp.replace(HINTS)')
    diagnostic_position=source.index("status=str(result['info'].get('status','')).lower()")
    assert native_position<write_position<replace_position<diagnostic_position
    assert source.index("out['solver_info']=clean(result['info'])")>replace_position
    assert "allow_nan=False" in source and "if isinstance(v,np.generic):return clean(v.item())" in source
    for fragment in ['LIMIT=1536*1024**2',"time.monotonic()-worker_began>90",
        "max(q.WorkingSetSize,q.PeakWorkingSetSize)>LIMIT",'process.terminate()',
        "W.HANDLE(int(process._handle))",'worker_began=time.monotonic();process=subprocess.Popen',
        'creationflags=getattr(subprocess,\'CREATE_NO_WINDOW\',0)',"'solver_retries':0",'time.sleep(.2)']:
        assert fragment in monitor
    assert monitor.index('worker_began=time.monotonic()')<monitor.index('process=subprocess.Popen')
    assert "'memory monitor unavailable for live worker; stopping only that PID'" in monitor

    preflight=json.loads((HERE/'independent-preflight.json').read_bytes())
    assert preflight['status']=='all181_exact_rows_old_adapter_and_every_CSR_float_independently_passed'
    assert preflight['source_sha256_start']==preflight['source_sha256_end']
    for name,h in preflight['source_sha256_start'].items():assert sha(ROOT/name)==h
    old=gzjson(oldpaths[0]);family=gzjson(oldpaths[1])
    rows=old['linear_rows']+family['additional_linear_rows'];assert len(rows)==5803
    old_nnz=0
    for row in rows:
        columns=[5004 if k==714 else k for k,v in row['coefficients']]
        assert len(columns)==len(set(columns)) and all(0<=k<5005 for k in columns)
        old_nnz+=len(columns)
    box_nnz=2*len(model['new_moment_boxes']);assert box_nnz==8580
    new_nnz=json.loads((CONE/'aggregation.json').read_bytes())['nonzero_numeric_coefficients'];assert new_nnz==905724
    target=array('H');target.frombytes((STATIC/'degree6-targets.bin').read_bytes())
    entries=array('I');entries.frombytes((STATIC/'degree6-entryplans.bin').read_bytes())
    if sys.byteorder!='little':target.byteswap();entries.byteswap()
    assert len(entries)==96580 and len(target)==1416525
    counts=[]
    for qid,shift,offset,count in model['entry_plans']:
        counts.append(sum(mid!=0 for mid in target[offset:offset+count]))
    psd_nnz=sum(counts[pid] for pid in entries)
    total_nnz=old_nnz+box_nnz+new_nnz+psd_nnz
    assert total_nnz==3153411
    sizes=[block['size'] for block in model['blocks']]
    assert sizes==[220]+[55]*46+[10]*26 and len(sizes)==73
    psd_rows=sum(n*(n+1)//2 for n in sizes);assert psd_rows==96580
    assert len(rows)+box_nnz+181==14564 and 14564+psd_rows==111144
    assert not any(name.split('.')[0] in ['numpy','scipy','scs'] for name in sys.modules)
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert initial==final
    def lineof(text,fragment):return text[:text.index(fragment)].count('\n')+1
    report={'scope':__doc__,'status':'frozen_worker_static_gate_passed_for_one_cold_CPU_direct_attempt',
        'source_sha256_start':initial,'source_sha256_end':final,'all_inputs_unchanged':True,
        'one_SCS_constructor_in_source':True,'one_SCS_solve_in_source':True,'constructor_line':constructors[0].lineno,
        'solve_line':solves[0].lineno,'solver_keywords':config,'solve_keywords':solve_config,
        'BLAS_threads_before_import':1,'optimization_variables':5005,'old_scalar_rows':14383,
        'new_unsoftened_scalar_rows':181,'total_scalar_rows':14564,'PSD_blocks':73,'PSD_packed_rows':96580,
        'matrix_shape':[111144,5005],'exact_nonzero_count':total_nnz,
        'nonzero_components':{'old_rows':old_nnz,'higher_moment_boxes':box_nnz,'new_rows':new_nnz,'PSD':psd_nnz},
        'retained_old_column_remap':[714,5004],'new_rows_slack_column_absent':True,
        'uniform_positive_block_scaling_and_SCS_sqrt2_sign_reviewed':True,
        'full_x_y_s_fsync_before_diagnostics':True,'durable_archive_write_line':lineof(source,'stream.write(compressed)'),
        'monitor_total_wall_seconds':90,'monitor_RSS_bytes':1536*1024**2,
        'monitor_tracks_only_created_process_handle':True,'monitor_includes_import_assembly_and_setup':True,
        'monitor_missing_memory_read_stops_only_worker':True,'retry_or_backend_fallback_in_source':False,
        'source_gate_only_not_worker_execution':True,'worker_executions':0,'solver_calls':0,'Lean_invocations':0,
        'strict_feasibility_or_exclusion_claimed':False,'global_floor_proved':False,'new_zero_proportion_proven':False,
        'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    if args.write_receipt:OUT.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:report[k] for k in ['status','matrix_shape','exact_nonzero_count','elapsed_milliseconds']}))


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
