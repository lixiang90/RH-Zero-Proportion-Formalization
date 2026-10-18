"""One root-gated independent stdlib child; no mathematical imports."""
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys
import time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def pin(p):return sha256(p.read_bytes()).hexdigest()
def save(n,x):
    with (HERE/n).open('x',encoding='utf8') as f:json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def size():return sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())
def main():
    p=argparse.ArgumentParser();p.add_argument('--launch-authorized-once',action='store_true');p.add_argument('--gate');p.add_argument('--gate-sha256');a=p.parse_args()
    assert a.launch_authorized_once and a.gate and a.gate_sha256
    for n in ['launch.json','child.json','started.json','independent-review.json','failure.json','terminal.json']:assert not (HERE/n).exists()
    gp=(ROOT/a.gate).resolve();assert gp.is_relative_to(ROOT) and pin(gp)==a.gate_sha256
    g=json.loads(gp.read_text(encoding='utf8'))
    assert type(g['independent_fixed_O_audits_authorized']) is int and g['independent_fixed_O_audits_authorized']==1
    assert g['automatic_retry_allowed'] is False
    limits=g['resource_limits'];assert limits['elapsed_seconds']>0 and limits['closed_output_bytes']>0
    cmd=[sys.executable,'-B','-X','utf8',str(HERE/'audit_once.py'),'--execute-authorized-audit-once','--gate',a.gate,'--gate-sha256',a.gate_sha256]
    save('launch.json',{'argv':cmd,'parent_pid':os.getpid(),'gate_sha256':a.gate_sha256,'auditor_sha256':pin(HERE/'audit_once.py'),'maximum_children':1,'resource_limits':limits})
    start=time.monotonic();reason=None
    with (HERE/'stdout.log').open('xb') as out,(HERE/'stderr.log').open('xb') as err:
        child=subprocess.Popen(cmd,cwd=ROOT,stdout=out,stderr=err)
        save('child.json',{'child_pid':child.pid,'parent_pid':os.getpid(),'child_launches':1})
        print(json.dumps({'child_pid':child.pid,'parent_pid':os.getpid(),'live':True}),flush=True)
        while child.poll() is None:
            if time.monotonic()-start>limits['elapsed_seconds']:reason='hard_time_limit'
            if size()>limits['closed_output_bytes']:reason='hard_output_limit'
            if reason:child.terminate();break
            time.sleep(.2)
        code=child.wait();out.flush();err.flush();os.fsync(out.fileno());os.fsync(err.fileno())
    started=json.loads((HERE/'started.json').read_text(encoding='utf8')) if (HERE/'started.json').exists() else {}
    endpoint={name:pin(ROOT/name) for name in started.get('inputs_sha256',{})}
    terminal={'child_pid':child.pid,'exit_code':code,'seconds':time.monotonic()-start,'limit_stop':reason,
        'child_launches':1,'automatic_retry':False,'closed_output_bytes':size(),'inputs_sha256_end_after_terminal':endpoint}
    save('terminal.json',terminal);print(json.dumps({k:v for k,v in terminal.items() if k!='inputs_sha256_end_after_terminal'}),flush=True)
    if code or reason:raise SystemExit(1)
if __name__=='__main__':main()
