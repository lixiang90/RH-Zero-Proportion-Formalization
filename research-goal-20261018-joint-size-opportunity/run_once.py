"""One fixed stdlib counting child; 60 seconds and2MB, no retry."""
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
def write(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def main():
    assert sys.argv[1:]==['--launch-authorized-size-audit']
    assert not (HERE/'launch.json').exists() and not (HERE/'started.json').exists()
    command=[sys.executable,str(HERE/'audit_once.py'),'--execute-fixed-size-audit'];identity={'argv':command,'cwd':str(ROOT)}
    write(HERE/'launch.json',{'schema':'fixed-margin-size-one-child-launch-v1','command':identity,
        'command_sha256':sha256(json.dumps(identity,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
        'script_sha256':pin(HERE/'audit_once.py'),'launcher_sha256':pin(Path(__file__)),
        'parent_pid':os.getpid(),'limits':{'seconds':60,'closed_output_bytes':2000000},'maximum_child_launches':1})
    t=time.monotonic();reason=None
    with (HERE/'stdout.log').open('xb') as out,(HERE/'stderr.log').open('xb') as err:
        proc=subprocess.Popen(command,cwd=ROOT,stdout=out,stderr=err)
        write(HERE/'child.json',{'child_pid':proc.pid,'parent_pid':os.getpid(),'child_launches':1,'time_unix':time.time()})
        print(json.dumps({'stage':'margin_size_audit_child_live','child_pid':proc.pid,'parent_pid':os.getpid()}),flush=True)
        while proc.poll() is None:
            if time.monotonic()-t>60:reason='elapsed_limit'
            elif sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())>2000000:reason='closed_output_limit'
            if reason:proc.terminate();break
            time.sleep(.1)
        code=proc.wait()
    status={'schema':'fixed-margin-size-audit-terminal-v1','child_pid':proc.pid,'exit_code':code,
        'seconds':time.monotonic()-t,'limit_stop':reason,'child_launches':1,'automatic_retry':False,
        'audit_present':(HERE/'audit.json').exists(),'failure_present':(HERE/'failure.json').exists(),
        'closed_output_bytes':sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())}
    write(HERE/'terminal.json',status);print(json.dumps(status),flush=True)
    if code or reason:raise SystemExit(1)

if __name__=='__main__':main()
