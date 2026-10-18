"""Prepared one-child bounded E launcher; no implicit execution or retry."""
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
def pin(p):return sha256(p.read_bytes()).hexdigest()
def write(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--launch-authorized-fixed-model',action='store_true')
    ap.add_argument('--gate');ap.add_argument('--gate-sha256');a=ap.parse_args()
    assert a.launch_authorized_fixed_model and a.gate and a.gate_sha256
    assert not (HERE/'launch.json').exists() and not (HERE/'started.json').exists()
    gate=(ROOT/a.gate).resolve();assert gate.is_relative_to(ROOT) and pin(gate)==a.gate_sha256
    cfg=json.loads(gate.read_text(encoding='utf-8'))
    assert cfg['pair_model_passes_authorized']==1 and cfg['resource_limits']=={'elapsed_seconds':300,'closed_output_bytes':20000000}
    command=[sys.executable,str(HERE/'model_once.py'),'--execute-authorized-fixed-model','--gate',a.gate,'--gate-sha256',a.gate_sha256]
    identity={'argv':command,'cwd':str(ROOT)}
    write(HERE/'launch.json',{'schema':'fixed-E-single-child-launch-v1','parent_pid':os.getpid(),'command':identity,
        'command_sha256':sha256(json.dumps(identity,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
        'script_sha256':pin(HERE/'model_once.py'),'launcher_sha256':pin(Path(__file__)),
        'maximum_child_launches':1,'time_limit_seconds':300,'closed_output_limit_bytes':20000000})
    start=time.monotonic();reason=None
    with (HERE/'stdout.log').open('xb') as out,(HERE/'stderr.log').open('xb') as err:
        proc=subprocess.Popen(command,cwd=ROOT,stdout=out,stderr=err)
        write(HERE/'child.json',{'child_pid':proc.pid,'parent_pid':os.getpid(),'child_launches':1,'time_unix':time.time()})
        print(json.dumps({'stage':'fixed_E_model_child_live','child_pid':proc.pid,'parent_pid':os.getpid()}),flush=True)
        while proc.poll() is None:
            if time.monotonic()-start>300:reason='elapsed_limit_inconclusive'
            elif sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())>20000000:reason='output_limit_inconclusive'
            if reason:proc.terminate();break
            time.sleep(.2)
        code=proc.wait()
    status={'schema':'fixed-E-terminal-v1','child_pid':proc.pid,'exit_code':code,'seconds':time.monotonic()-start,
        'limit_stop':reason,'child_launches':1,'automatic_retry':False,'model_receipt_present':(HERE/'model.json').exists(),
        'inconclusive':bool(reason) or (HERE/'inconclusive.json').exists(),
        'closed_output_bytes':sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())}
    write(HERE/'terminal.json',status);print(json.dumps(status),flush=True)
    if code or reason:raise SystemExit(1)

if __name__=='__main__':main()
