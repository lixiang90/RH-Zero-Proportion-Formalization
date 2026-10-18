"""Prepared O single fixed curvature opportunity child. Hard limits supplied by immutable root gate."""
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
def pin(p):
    h=sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):h.update(block)
    return h.hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def write(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def size():return sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--launch-authorized-fixed-curvature-O',action='store_true')
    ap.add_argument('--gate');ap.add_argument('--gate-sha256');a=ap.parse_args()
    assert a.launch_authorized_fixed_curvature_O and a.gate and a.gate_sha256
    for name in ['launch.json','child.json','started.json','result.json','failure.json','terminal.json','inconclusive.json']:
        assert not (HERE/name).exists(),('existing_attempt_no_retry',name)
    gate=(ROOT/a.gate).resolve();assert gate.is_relative_to(ROOT) and pin(gate)==a.gate_sha256;g=load(gate)
    assert g['fixed_curvature_opportunity_passes_authorized']==1 and g['fixed_G_index']==1322606
    assert g['source_CellA_quantitative_replay_authorized'] is True
    assert g['new_kernel_anchors_FS_solver_or_Lean_authorized']==0
    hard=g['resource_limits'];soft=g['work_limits']
    assert 0<soft['elapsed_seconds']<hard['elapsed_seconds']
    assert 0<soft['closed_output_bytes']<hard['closed_output_bytes']
    command=[sys.executable,'-B','-X','utf8',str(HERE/'audit_once.py'),
        '--execute-authorized-fixed-curvature-O','--gate',a.gate,'--gate-sha256',a.gate_sha256]
    env=dict(os.environ);env.update(THREAD_ENV);env['PYTHONDONTWRITEBYTECODE']='1'
    identity={'argv':command,'cwd':str(ROOT),'thread_env_override':THREAD_ENV}
    write(HERE/'launch.json',{'schema':'O-single-child-launch-v1','parent_pid':os.getpid(),
        'command':identity,'command_sha256':sha256(json.dumps(identity,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
        'discover_source_sha256':pin(HERE/'audit_once.py'),'launcher_sha256':pin(Path(__file__)),
        'gate_path':a.gate,'gate_sha256':a.gate_sha256,'maximum_child_launches':1,'hard_limits':hard})
    start=time.monotonic();reason=None
    with (HERE/'stdout.log').open('xb') as out,(HERE/'stderr.log').open('xb') as err:
        proc=subprocess.Popen(command,cwd=ROOT,env=env,stdout=out,stderr=err)
        write(HERE/'child.json',{'child_pid':proc.pid,'parent_pid':os.getpid(),'time_unix':time.time(),'launches':1})
        print(json.dumps({'stage':'O_child_live','child_pid':proc.pid,'parent_pid':os.getpid()}),flush=True)
        while proc.poll() is None:
            if time.monotonic()-start>hard['elapsed_seconds']:reason='hard_elapsed_limit_inconclusive'
            elif size()>hard['closed_output_bytes']:reason='hard_output_limit_inconclusive'
            if reason:proc.terminate();break
            time.sleep(.2)
        code=proc.wait()
        for f in [out,err]:f.flush();os.fsync(f.fileno())
    started=load(HERE/'started.json') if (HERE/'started.json').exists() else {}
    endpoint={name:pin(ROOT/name) for name in started.get('inputs_sha256',{})}
    external={name:pin(Path(name)) for name in started.get('external_runtime_sha256_start',{})}
    terminal={'schema':'O-single-child-terminal-v1','child_pid':proc.pid,'parent_pid':os.getpid(),
        'exit_code':code,'seconds':time.monotonic()-start,'limit_stop':reason,'child_launches':1,
        'automatic_retry':False,'closed_output_bytes':size(),
        'result_present':(HERE/'result.json').exists(),'failure_present':(HERE/'failure.json').exists(),
        'inconclusive_present':(HERE/'inconclusive.json').exists(),
        'curvature_packet_sha256':pin(HERE/'curvature-packet.json') if (HERE/'curvature-packet.json').exists() else None,
        'inputs_sha256_end_after_terminal':endpoint,'external_runtime_sha256_end_after_terminal':external,
        'inputs_unchanged_after_terminal':endpoint==started.get('inputs_sha256',{}),
        'external_runtime_unchanged_after_terminal':external==started.get('external_runtime_sha256_start',{})}
    write(HERE/'terminal.json',terminal)
    print(json.dumps({k:v for k,v in terminal.items() if 'sha256_end' not in k}),flush=True)
    if code or reason or not terminal['inputs_unchanged_after_terminal'] or not terminal['external_runtime_unchanged_after_terminal']:raise SystemExit(1)
if __name__=='__main__':main()
