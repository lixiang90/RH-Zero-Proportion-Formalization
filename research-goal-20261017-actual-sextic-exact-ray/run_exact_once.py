"""Run one exact combination, monitoring only its own PID for1.5GiB RSS.

No optimizer, fallback, retry, parameter or precision change is allowed.
The integer-Gram factors already exist from the sole73-block eig pass.
"""
from pathlib import Path
from ctypes import wintypes as W
import ctypes,hashlib,json,subprocess,sys,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;OUT=HERE/'exact-monitor.json';LIMIT=1536*1024**2
class PMC(ctypes.Structure):
    _fields_=[('cb',W.DWORD),('PageFaultCount',W.DWORD)]+[(s,ctypes.c_size_t) for s in
        ['PeakWorkingSetSize','WorkingSetSize','QuotaPeakPagedPoolUsage','QuotaPagedPoolUsage','QuotaPeakNonPagedPoolUsage','QuotaNonPagedPoolUsage','PagefileUsage','PeakPagefileUsage']]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not OUT.exists() and not (HERE/'exact-combination.json').exists();began=time.monotonic()
paths=[Path(__file__),HERE/'combine_ray.py',HERE/'quantized-ray.json.gz'];initial={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
report={'scope':__doc__,'source_sha256_start':initial,'worker_processes_launched':0,'optimizer_calls':0,'retries':0,
    'memory_limit_bytes':LIMIT,'snapshots':[],'termination_reason':None,'terminated_only_worker_PID':None}
def save():
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==initial
    report.update({'source_sha256_end':final,'all_inputs_unchanged':True,'elapsed_milliseconds':int((time.monotonic()-began)*1000)})
    tmp=OUT.with_suffix('.partial');tmp.write_text(json.dumps(report,separators=(',',':'))+'\n',encoding='utf8');tmp.replace(OUT)
save();psapi=ctypes.WinDLL('psapi');psapi.GetProcessMemoryInfo.argtypes=[W.HANDLE,ctypes.POINTER(PMC),W.DWORD]
with (HERE/'exact-stdout.log').open('w',encoding='utf8') as stdout,(HERE/'exact-stderr.log').open('w',encoding='utf8') as stderr:
    process=subprocess.Popen([sys.executable,str(HERE/'combine_ray.py')],cwd=str(ROOT),stdout=stdout,stderr=stderr,
        creationflags=getattr(subprocess,'CREATE_NO_WINDOW',0))
    report.update({'PID':process.pid,'worker_processes_launched':1});save();last=time.monotonic()
    try:
        while process.poll() is None:
            q=PMC();q.cb=ctypes.sizeof(q)
            if psapi.GetProcessMemoryInfo(W.HANDLE(int(process._handle)),ctypes.byref(q),q.cb):
                point={'elapsed_milliseconds':int((time.monotonic()-began)*1000),'working_set_bytes':q.WorkingSetSize,
                    'peak_working_set_bytes':q.PeakWorkingSetSize};report['snapshots'].append(point)
                if max(q.WorkingSetSize,q.PeakWorkingSetSize)>LIMIT:
                    report.update({'terminated_only_worker_PID':process.pid,'termination_reason':'ownPID current/peakRSS exceeded1.5GiB'});save();process.terminate();break
            elif process.poll() is None:
                report.update({'terminated_only_worker_PID':process.pid,'termination_reason':'live ownPID memory monitoring unavailable'});save();process.terminate();break
            if time.monotonic()-last>1:save();last=time.monotonic()
            time.sleep(.2)
    except BaseException as exc:
        report['monitor_exception']=repr(exc)
        if process.poll() is None:
            report.update({'terminated_only_worker_PID':process.pid,'termination_reason':'monitor exception, stopped ownPID'});process.terminate()
    report['worker_exit_code']=process.wait()
report['phase']='single_exact_worker_terminal'
if report['snapshots']:report['observed_peak_working_set_bytes']=max(p['peak_working_set_bytes'] for p in report['snapshots'])
save();print(json.dumps({k:report.get(k) for k in ['phase','worker_exit_code','termination_reason','observed_peak_working_set_bytes','elapsed_milliseconds']}),flush=True)
