"""One small owned-Python-child Win32 memory-API observation; no Lean or candidate."""
from pathlib import Path
from ctypes import wintypes
import ctypes
import json
import os
import subprocess
import sys
import time

class Counters(ctypes.Structure):
    _fields_ = [('cb', wintypes.DWORD), ('PageFaultCount', wintypes.DWORD)] + [
        (n, ctypes.c_size_t) for n in ['PeakWorkingSetSize','WorkingSetSize','QuotaPeakPagedPoolUsage',
        'QuotaPagedPoolUsage','QuotaPeakNonPagedPoolUsage','QuotaNonPagedPoolUsage','PagefileUsage',
        'PeakPagefileUsage','PrivateUsage']]

api = ctypes.WinDLL('psapi', use_last_error=True).GetProcessMemoryInfo
api.argtypes = [wintypes.HANDLE, ctypes.c_void_p, wintypes.DWORD]
api.restype = wintypes.BOOL
child = subprocess.Popen([sys.executable, '-c', 'import time; b=bytearray(64*1024*1024); b[::4096]=b"x"*len(b[::4096]); time.sleep(0.7)'],
    stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
    creationflags=subprocess.CREATE_NO_WINDOW, shell=False)
def memory():
    c = Counters()
    c.cb = ctypes.sizeof(c)
    if not api(wintypes.HANDLE(int(child._handle)), ctypes.byref(c), c.cb):
        raise OSError(ctypes.get_last_error(), 'GetProcessMemoryInfo failed')
    return {n:int(getattr(c,n)) for n in ['PeakWorkingSetSize','WorkingSetSize','PeakPagefileUsage','PrivateUsage']}
samples=[]
try:
    deadline=time.monotonic()+10
    while child.poll() is None:
        samples.append(memory())
        if time.monotonic()>deadline:
            raise TimeoutError('Owned Python probe timeout')
        time.sleep(0.05)
    child.wait()
    after=memory()
finally:
    if child.poll() is None:
        child.kill()
        child.wait()
assert child.returncode==0 and samples
assert max(r['PeakPagefileUsage'] for r in samples)>64*1024*1024
assert after['PeakPagefileUsage']>64*1024*1024
result={'schema':'owned-python-child-Win32-memory-api-observation-v1',
    'scope':'Small 64MiB Python-child API exercise only. No Lean, candidate, resource runner, compiler or kernel executed.',
    'owned_child_pid':child.pid,'actual_child_wait_exit_code':child.returncode,'sample_count':len(samples),
    'counter_structure_bytes':ctypes.sizeof(Counters),'post_wait_query_succeeded':True,
    'maximum_sampled_peak_working_set':max(r['PeakWorkingSetSize'] for r in samples),
    'maximum_sampled_peak_process_commit':max(r['PeakPagefileUsage'] for r in samples),
    'post_wait_counters':after,'actual_parent_exit_observed_externally':None}
output=Path(__file__).with_name('receipt.json')
with output.open('xb') as stream:
    stream.write((json.dumps(result,indent=2)+'\n').encode())
    stream.flush()
    os.fsync(stream.fileno())
print(json.dumps(result),flush=True)
