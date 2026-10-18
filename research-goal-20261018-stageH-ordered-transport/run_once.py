"""Prepared H single-child launcher; hard300s/20MB; no retry."""
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
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--launch-authorized-H',action='store_true')
    ap.add_argument('--gate');ap.add_argument('--gate-sha256');a=ap.parse_args()
    assert a.launch_authorized_H and a.gate and a.gate_sha256
    assert not (HERE/'launch.json').exists() and not (HERE/'started.json').exists()
    gate=(ROOT/a.gate).resolve();assert gate.is_relative_to(ROOT) and pin(gate)==a.gate_sha256
    g=json.loads(gate.read_text(encoding='utf-8'))
    assert g['ordered_transport_classification_passes_authorized']==1
    assert g['resource_limits']=={'elapsed_seconds':300,'closed_output_bytes':20000000}
    assert g['work_limits']=={'elapsed_seconds':270,'closed_output_bytes':19000000}
    command=[sys.executable,str(HERE/'classify_once.py'),'--execute-authorized-H','--gate',a.gate,'--gate-sha256',a.gate_sha256]
    identity={'argv':command,'cwd':str(ROOT)}
    write(HERE/'launch.json',{'schema':'H-one-child-launch-v1','command':identity,
        'command_sha256':sha256(json.dumps(identity,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
        'parent_pid':os.getpid(),'script_sha256':pin(HERE/'classify_once.py'),'launcher_sha256':pin(Path(__file__)),
        'maximum_child_launches':1,'hard_limits':g['resource_limits'],'soft_work_limits':g['work_limits']})
    t=time.monotonic();reason=None
    with (HERE/'stdout.log').open('xb') as out,(HERE/'stderr.log').open('xb') as err:
        proc=subprocess.Popen(command,cwd=ROOT,stdout=out,stderr=err)
        write(HERE/'child.json',{'child_pid':proc.pid,'parent_pid':os.getpid(),'time_unix':time.time(),'child_launches':1})
        print(json.dumps({'stage':'H_child_live','child_pid':proc.pid,'parent_pid':os.getpid()}),flush=True)
        while proc.poll() is None:
            if time.monotonic()-t>300:reason='hard_elapsed_limit_inconclusive'
            elif sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())>20000000:reason='hard_output_limit_inconclusive'
            if reason:proc.terminate();break
            time.sleep(.2)
        code=proc.wait()
    prefix=json.loads((HERE/'prefix.json').read_text()) if (HERE/'prefix.json').exists() else None
    status={'schema':'H-one-child-terminal-v1','child_pid':proc.pid,'exit_code':code,'seconds':time.monotonic()-t,
        'limit_stop':reason,'child_launches':1,'automatic_retry':False,
        'classification_receipt_present':(HERE/'result.json').exists(),
        'published_prefix_records':prefix['committed_records'] if prefix else 0,
        'published_prefix_sha256':pin(HERE/'prefix.json') if prefix else None,
        'failure_present':(HERE/'failure.json').exists(),
        'closed_output_bytes':sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())}
    write(HERE/'terminal.json',status);print(json.dumps(status),flush=True)
    if code or reason:raise SystemExit(1)

if __name__=='__main__':main()
