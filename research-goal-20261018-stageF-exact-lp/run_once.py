"""Prepared bounded one-child exact F launcher; no implicit retry or solve."""
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
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--launch-authorized-fixed-F',action='store_true')
    ap.add_argument('--gate');ap.add_argument('--gate-sha256');a=ap.parse_args()
    assert a.launch_authorized_fixed_F and a.gate and a.gate_sha256
    assert not (HERE/'launch.json').exists() and not (HERE/'started.json').exists()
    gate=(ROOT/a.gate).resolve();assert gate.is_relative_to(ROOT) and pin(gate)==a.gate_sha256
    cfg=json.loads(gate.read_text(encoding='utf-8'))
    assert cfg['primary_simplex_calls_authorized']==1
    assert cfg['conditional_farkas_calls_authorized'] in [0,1]
    assert cfg['max_simplex_calls']==1+cfg['conditional_farkas_calls_authorized']
    limits=cfg['resource_limits'];assert 0<limits['elapsed_seconds']<=300 and 0<limits['closed_output_bytes']<=20000000
    command=[sys.executable,str(HERE/'solve_fixed_once.py'),'--execute-authorized-fixed-F','--gate',a.gate,'--gate-sha256',a.gate_sha256]
    identity={'argv':command,'cwd':str(ROOT)}
    write(HERE/'launch.json',{'schema':'fixed-F-single-child-launch-v1','command':identity,
        'command_sha256':sha256(json.dumps(identity,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
        'parent_pid':os.getpid(),'script_sha256':pin(HERE/'solve_fixed_once.py'),'launcher_sha256':pin(Path(__file__)),
        'primary_calls_authorized':1,'conditional_auxiliary_calls_authorized':cfg['conditional_farkas_calls_authorized'],
        'maximum_child_launches':1,'resource_limits':limits})
    start=time.monotonic();reason=None
    with (HERE/'stdout.log').open('xb') as out,(HERE/'stderr.log').open('xb') as err:
        proc=subprocess.Popen(command,cwd=ROOT,stdout=out,stderr=err)
        write(HERE/'child.json',{'child_pid':proc.pid,'parent_pid':os.getpid(),'time_unix':time.time(),'child_launches':1})
        print(json.dumps({'stage':'fixed_F_exact_child_live','child_pid':proc.pid,'parent_pid':os.getpid()}),flush=True)
        while proc.poll() is None:
            if time.monotonic()-start>limits['elapsed_seconds']:reason='elapsed_limit_inconclusive'
            elif sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())>limits['closed_output_bytes']:reason='output_limit_inconclusive'
            if reason:proc.terminate();break
            time.sleep(.2)
        code=proc.wait()
    result=HERE/'result.json'
    status={'schema':'fixed-F-terminal-v1','child_pid':proc.pid,'exit_code':code,'seconds':time.monotonic()-start,
        'limit_stop':reason,'child_launches':1,'automatic_retry':False,
        'primary_call_marker_present':(HERE/'primary-call-started.json').exists(),
        'conditional_auxiliary_call_marker_present':(HERE/'auxiliary-call-started.json').exists(),
        'result_present':result.exists(),'failure_present':(HERE/'failure.json').exists(),
        'closed_output_bytes':sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())}
    write(HERE/'terminal.json',status);print(json.dumps(status),flush=True)
    if code or reason:raise SystemExit(1)

if __name__=='__main__':main()
