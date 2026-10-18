"""One child, 180 seconds, closed output cap 32MB; no automatic retry."""
from pathlib import Path
from hashlib import sha256
import json
import os
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent

def pin(p):return sha256(p.read_bytes()).hexdigest()
def write(path,data):
    with path.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(data,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())

def main():
    assert __debug__ and sys.argv[1:]==['--launch-authorized-fixed-B']
    assert not (HERE/'launch.json').exists() and not (HERE/'started.json').exists()
    script=HERE/'stageB_classify_once.py';cmd=[sys.executable,str(script),'--execute-fixed-stage-B']
    identity={'argv':cmd,'cwd':str(ROOT)}
    write(HERE/'launch.json',{'schema':'one-fixed-StageB-launch-v1','parent_pid':os.getpid(),
        'command':identity,'command_sha256':sha256(json.dumps(identity,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
        'script_sha256':pin(script),'launcher_sha256':pin(Path(__file__)),
        'time_limit_seconds':180,'closed_output_limit_bytes':32000000,'maximum_child_launches':1})
    t=time.monotonic();reason=None
    with (HERE/'stdout.log').open('xb') as out,(HERE/'stderr.log').open('xb') as err:
        proc=subprocess.Popen(cmd,cwd=ROOT,stdout=out,stderr=err)
        write(HERE/'child.json',{'child_pid':proc.pid,'parent_pid':os.getpid(),'child_launches':1,'time_unix':time.time()})
        print(json.dumps({'stage':'StageB_child_live','pid':proc.pid,'parent_pid':os.getpid(),
            'script_sha256':pin(script)}),flush=True)
        while proc.poll() is None:
            seconds=time.monotonic()-t
            nbytes=sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())
            if seconds>180 or nbytes>32000000:
                reason='elapsed_limit' if seconds>180 else 'closed_output_limit'
                proc.terminate();break
            time.sleep(.2)
        code=proc.wait()
    status={'schema':'one-fixed-StageB-terminal-v1','child_pid':proc.pid,'exit_code':code,
        'seconds':time.monotonic()-t,'limit_stop':reason,'child_launches':1,'automatic_retry':False,
        'classification_receipt_present':(HERE/'classification.json').exists(),
        'failure_receipt_present':(HERE/'failure.json').exists(),
        'closed_output_bytes':sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())}
    write(HERE/'terminal.json',status);print(json.dumps(status),flush=True)
    if code or reason:raise SystemExit(1)

if __name__=='__main__':main()
