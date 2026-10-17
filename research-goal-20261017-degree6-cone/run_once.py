"""Launch and monitor exactly one isolated degree6 SCS worker PID.

Monitor only that process with Windows GetProcessMemoryInfo. If its
current/peak working set exceeds1.5GiB, terminate only that PID and record
the reason. No process-name kill, retry, solver fallback or settings scan.
"""
from pathlib import Path
import ctypes,hashlib,json,os,subprocess,sys,time
from ctypes import wintypes as W
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;OUT=HERE/'monitor.json';LIMIT=1536*1024**2
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
class PMC(ctypes.Structure):
    _fields_=[('cb',W.DWORD),('PageFaultCount',W.DWORD)]+[(s,ctypes.c_size_t) for s in
        ['PeakWorkingSetSize','WorkingSetSize','QuotaPeakPagedPoolUsage','QuotaPagedPoolUsage','QuotaPeakNonPagedPoolUsage','QuotaNonPagedPoolUsage','PagefileUsage','PeakPagefileUsage']]
def main():
    assert not OUT.exists() and not (HERE/'worker-receipt.json').exists();began=time.monotonic()
    paths=[Path(__file__),HERE/'worker.py',ROOT/'research-goal-20261017-degree6-static/degree6-files.json']
    pins={p.relative_to(ROOT).as_posix():sha(p) for p in paths};env=os.environ.copy()
    for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:env[k]='1'
    out={'scope':__doc__,'phase':'before_single_worker','input_sha256_start':pins,'memory_limit_bytes':LIMIT,
        'worker_processes_launched':0,'snapshots':[],'terminated_only_worker_PID':None,'termination_reason':None,
        'solver_retries':0,'Lean_invocations':0,'cell_exclusion_proven':False,'new_zero_proportion_proven':False}
    def save():
        final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==pins
        out.update({'input_sha256_end':final,'all_inputs_unchanged':True,'elapsed_milliseconds':int((time.monotonic()-began)*1000)})
        temp=OUT.with_suffix('.json.partial');temp.write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8');temp.replace(OUT)
    save();psapi=ctypes.WinDLL('psapi',use_last_error=True)
    psapi.GetProcessMemoryInfo.argtypes=[W.HANDLE,ctypes.POINTER(PMC),W.DWORD]
    with (HERE/'worker-stdout.log').open('w',encoding='utf8') as stdout,(HERE/'worker-stderr.log').open('w',encoding='utf8') as stderr:
        process=subprocess.Popen([sys.executable,str(HERE/'worker.py')],cwd=str(ROOT),env=env,stdout=stdout,stderr=stderr,
            creationflags=getattr(subprocess,'CREATE_NO_WINDOW',0))
        out.update({'phase':'monitoring_single_worker','PID':process.pid,'worker_processes_launched':1});save();last_save=time.monotonic()
        try:
            while process.poll() is None:
                q=PMC();q.cb=ctypes.sizeof(q)
                if psapi.GetProcessMemoryInfo(W.HANDLE(int(process._handle)),ctypes.byref(q),q.cb):
                    point={'elapsed_milliseconds':int((time.monotonic()-began)*1000),'working_set_bytes':q.WorkingSetSize,
                        'peak_working_set_bytes':q.PeakWorkingSetSize,'private_commit_bytes':q.PagefileUsage};out['snapshots'].append(point)
                    if max(q.WorkingSetSize,q.PeakWorkingSetSize)>LIMIT:
                        out['terminated_only_worker_PID']=process.pid;out['termination_reason']='worker current/peak RSS exceeded1.5GiB';save()
                        process.terminate();break
                elif process.poll() is None:
                    out['terminated_only_worker_PID']=process.pid;out['termination_reason']='memory monitor unavailable for live worker; stopping only that PID';save()
                    process.terminate();break
                if time.monotonic()-last_save>1:save();last_save=time.monotonic()
                time.sleep(.2)
        except BaseException as exc:
            out['monitor_exception']=repr(exc)
            if process.poll() is None:
                out['terminated_only_worker_PID']=process.pid;out['termination_reason']='monitor exception; stopped only own worker PID';process.terminate()
        code=process.wait();out['worker_exit_code']=code
    if out['snapshots']:out['observed_peak_working_set_bytes']=max(p['peak_working_set_bytes'] for p in out['snapshots'])
    receipt=HERE/'worker-receipt.json'
    if receipt.exists():
        q=json.loads(receipt.read_bytes());out['worker_receipt_sha256']=sha(receipt);out['worker_final_phase']=q['phase'];out['SCS_solve_calls_recorded']=q.get('SCS_solve_calls',0)
    out['phase']='single_worker_monitor_complete';save()
    print(json.dumps({k:out.get(k) for k in ['phase','PID','worker_exit_code','observed_peak_working_set_bytes','termination_reason','worker_final_phase','SCS_solve_calls_recorded','elapsed_milliseconds']}),flush=True)
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
