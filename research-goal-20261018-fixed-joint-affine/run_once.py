"""Single authorized rational arithmetic child, 60 seconds/8MB, no retry."""
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
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--launch-authorized-once',action='store_true')
    ap.add_argument('--gate');ap.add_argument('--gate-sha256');args=ap.parse_args()
    assert args.launch_authorized_once and args.gate and args.gate_sha256
    assert not (HERE/'launch.json').exists() and not (HERE/'started.json').exists()
    gate=(ROOT/args.gate).resolve();assert gate.is_relative_to(ROOT) and pin(gate)==args.gate_sha256
    cfg=json.loads(gate.read_text(encoding='utf-8'))
    assert cfg['affine_evaluations_authorized']==1 and cfg['resource_limits']=={'elapsed_seconds':60,'closed_output_bytes':8000000}
    command=[sys.executable,str(HERE/'evaluate_once.py'),'--execute-authorized-once','--gate',args.gate,'--gate-sha256',args.gate_sha256]
    identity={'argv':command,'cwd':str(ROOT)}
    write(HERE/'launch.json',{'schema':'fixed-two-FS-affine-single-launch-v1','parent_pid':os.getpid(),
        'command':identity,'command_sha256':sha256(json.dumps(identity,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
        'script_sha256':pin(HERE/'evaluate_once.py'),'launcher_sha256':pin(Path(__file__)),
        'maximum_child_launches':1,'limits':{'seconds':60,'closed_output_bytes':8000000}})
    start=time.monotonic();reason=None
    with (HERE/'stdout.log').open('xb') as out,(HERE/'stderr.log').open('xb') as err:
        proc=subprocess.Popen(command,cwd=ROOT,stdout=out,stderr=err)
        write(HERE/'child.json',{'child_pid':proc.pid,'parent_pid':os.getpid(),'time_unix':time.time(),'child_launches':1})
        print(json.dumps({'stage':'fixed_two_FS_affine_child_live','child_pid':proc.pid,'parent_pid':os.getpid()}),flush=True)
        while proc.poll() is None:
            if time.monotonic()-start>60:reason='elapsed_limit'
            elif sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())>8000000:reason='closed_output_limit'
            if reason:proc.terminate();break
            time.sleep(.1)
        code=proc.wait()
    status={'schema':'fixed-two-FS-affine-terminal-v1','child_pid':proc.pid,'exit_code':code,
        'seconds':time.monotonic()-start,'limit_stop':reason,'child_launches':1,'automatic_retry':False,
        'evaluation_present':(HERE/'evaluation.json').exists(),'failure_present':(HERE/'failure.json').exists(),
        'closed_output_bytes':sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())}
    write(HERE/'terminal.json',status);print(json.dumps(status),flush=True)
    if code or reason:raise SystemExit(1)

if __name__=='__main__':main()
