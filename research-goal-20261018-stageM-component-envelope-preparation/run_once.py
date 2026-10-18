"""Prepared M: one child, hard300s/20MB, no retries or auxiliary optimizer."""
from pathlib import Path
from hashlib import sha256
import argparse
import json
import os
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
THREAD_ENV={name:'1' for name in ['OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS',
    'NUMEXPR_NUM_THREADS','VECLIB_MAXIMUM_THREADS','BLIS_NUM_THREADS']}
def pin(p):return sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def write(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def size():return sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--launch-authorized-fixed-M',action='store_true')
    ap.add_argument('--gate');ap.add_argument('--gate-sha256');a=ap.parse_args()
    assert a.launch_authorized_fixed_M and a.gate and a.gate_sha256
    for name in ['launch.json','child.json','started.json','result.json','failure.json','terminal.json']:
        assert not (HERE/name).exists(),('previous_attempt',name)
    gate=(ROOT/a.gate).resolve();assert gate.is_relative_to(ROOT) and pin(gate)==a.gate_sha256;g=load(gate)
    assert g['component_envelope_LP_passes_authorized']==1 and g['primary_linprog_calls_authorized']==1
    assert g['auxiliary_optimization_calls_authorized']==0
    assert g['resource_limits']=={'elapsed_seconds':300,'closed_output_bytes':20000000}
    command=[sys.executable,'-B','-X','utf8',str(HERE/'discover_once.py'),'--execute-authorized-fixed-M',
        '--gate',a.gate,'--gate-sha256',a.gate_sha256]
    env=dict(os.environ);env.update(THREAD_ENV);env['PYTHONDONTWRITEBYTECODE']='1'
    identity={'argv':command,'cwd':str(ROOT),'thread_env_override':THREAD_ENV}
    write(HERE/'launch.json',{'schema':'M-one-child-launch-v1','command':identity,
        'command_sha256':sha256(json.dumps(identity,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
        'parent_pid':os.getpid(),'child_launches_authorized':1,'hard_limits':g['resource_limits'],
        'script_sha256':pin(HERE/'discover_once.py'),'launcher_sha256':pin(Path(__file__))})
    start=time.monotonic();reason=None
    with (HERE/'stdout.log').open('xb') as out,(HERE/'stderr.log').open('xb') as err:
        proc=subprocess.Popen(command,cwd=ROOT,env=env,stdout=out,stderr=err)
        write(HERE/'child.json',{'child_pid':proc.pid,'parent_pid':os.getpid(),'child_launches':1,'time_unix':time.time()})
        print(json.dumps({'stage':'M_child_live','child_pid':proc.pid,'parent_pid':os.getpid()}),flush=True)
        while proc.poll() is None:
            if time.monotonic()-start>300:reason='hard_elapsed300_inconclusive'
            elif size()>20000000:reason='hard_output20MB_inconclusive'
            if reason:proc.terminate();break
            time.sleep(.2)
        code=proc.wait()
        for f in [out,err]:f.flush();os.fsync(f.fileno())
    started=load(HERE/'started.json') if (HERE/'started.json').exists() else {}
    endpoints={name:pin(ROOT/name) for name in started.get('inputs_sha256',{})}
    external={name:pin(Path(name)) for name in started.get('external_runtime_sha256_start',{})}
    terminal={'schema':'M-one-child-terminal-v1','child_pid':proc.pid,'parent_pid':os.getpid(),'exit_code':code,
        'seconds':time.monotonic()-start,'limit_stop':reason,'child_launches':1,'automatic_retry':False,
        'closed_output_bytes':size(),'result_present':(HERE/'result.json').exists(),'failure_present':(HERE/'failure.json').exists(),
        'inputs_sha256_end_after_child_terminal':endpoints,'external_runtime_sha256_end_after_child_terminal':external}
    write(HERE/'terminal.json',terminal)
    print(json.dumps({k:v for k,v in terminal.items() if 'sha256_end' not in k}),flush=True)
    if code or reason:raise SystemExit(1)

if __name__=='__main__':main()
