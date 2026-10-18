"""Prepared J one-child launcher; hard300s/20MB, no retry or solver."""
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
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def write(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def size():return sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())
def endpoint_hashes():
    p=HERE/'started.json'
    if not p.exists():return {}
    refs=load(p)['inputs_sha256']
    return {name:pin(ROOT/name) for name in refs}
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--launch-authorized-fixed-J',action='store_true')
    ap.add_argument('--gate');ap.add_argument('--gate-sha256');a=ap.parse_args()
    assert a.launch_authorized_fixed_J and a.gate and a.gate_sha256
    for name in ['launch.json','child.json','started.json','result.json','terminal.json','failure.json']:
        assert not (HERE/name).exists(),('previous_attempt',name)
    gate=(ROOT/a.gate).resolve();assert gate.is_relative_to(ROOT) and pin(gate)==a.gate_sha256
    g=load(gate)
    assert g['fixed_basis_classification_passes_authorized']==1
    assert g['resource_limits']=={'elapsed_seconds':300,'closed_output_bytes':20000000}
    assert g['work_limits']=={'elapsed_seconds':270,'closed_output_bytes':19000000}
    assert g['new_FS_kernel_points_LP_or_Lean_authorized']==0
    command=[sys.executable,'-B','-X','utf8',str(HERE/'classify_once.py'),
        '--execute-authorized-fixed-J','--gate',a.gate,'--gate-sha256',a.gate_sha256]
    identity={'argv':command,'cwd':str(ROOT)}
    write(HERE/'launch.json',{'schema':'J-one-child-launch-v1','command':identity,
        'command_sha256':sha256(json.dumps(identity,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
        'parent_pid':os.getpid(),'script_sha256':pin(HERE/'classify_once.py'),
        'launcher_sha256':pin(Path(__file__)),'maximum_child_launches':1,'hard_limits':g['resource_limits']})
    start=time.monotonic();reason=None
    with (HERE/'stdout.log').open('xb') as out,(HERE/'stderr.log').open('xb') as err:
        proc=subprocess.Popen(command,cwd=ROOT,stdout=out,stderr=err)
        write(HERE/'child.json',{'child_pid':proc.pid,'parent_pid':os.getpid(),'time_unix':time.time(),'child_launches':1})
        print(json.dumps({'stage':'J_child_live','child_pid':proc.pid,'parent_pid':os.getpid()}),flush=True)
        while proc.poll() is None:
            if time.monotonic()-start>300:reason='hard_elapsed_limit_inconclusive'
            elif size()>20000000:reason='hard_output_limit_inconclusive'
            if reason:proc.terminate();break
            time.sleep(.2)
        code=proc.wait()
        for f in [out,err]:f.flush();os.fsync(f.fileno())
    end_hashes=endpoint_hashes()
    status={'schema':'J-one-child-terminal-v1','child_pid':proc.pid,'exit_code':code,
        'seconds':time.monotonic()-start,'limit_stop':reason,'child_launches':1,'automatic_retry':False,
        'result_present':(HERE/'result.json').exists(),'failure_present':(HERE/'failure.json').exists(),
        'inconclusive_present':(HERE/'inconclusive.json').exists(),'closed_output_bytes':size(),
        'inputs_sha256_end_after_child_terminal':end_hashes}
    write(HERE/'terminal.json',status);print(json.dumps(status),flush=True)
    if code or reason:raise SystemExit(1)

if __name__=='__main__':main()
