"""One explicitly gated versioned repair plus the previously unrun Sparse78."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import time
from compile_phaseA import ROOT, HERE, LINUX, LEAN, PINS, DEPENDENCY_LIB, sha, save_new, wsl


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--gate',required=True)
    ap.add_argument('--gate-sha256',required=True)
    ns=ap.parse_args()
    gp=ROOT/ns.gate
    assert sha(gp)==ns.gate_sha256
    gate=json.loads(gp.read_text(encoding='utf-8'))
    manifest=HERE/'phaseA1-prepared.json'
    assert gate['authorized'] is True and gate['task']=='stageM-actual-Lean-phaseA1'
    assert gate['prepared_manifest_sha256']==sha(manifest)
    assert gate['automatic_repairs_or_retries']==0 and gate['repeat_CurrentPrefix'] is False
    prep=json.loads(manifest.read_text(encoding='utf-8'))
    for row in prep['files']+prep['dependencies']:
        assert sha(ROOT/row['path'])==row['sha256'],row['path']
    assert sha(prep['Python_executable']['path'])==prep['Python_executable']['sha256']
    ps=subprocess.run(wsl('/usr/bin/pgrep','-a','-x','lean'),capture_output=True)
    assert ps.returncode==1 and not ps.stdout,'another Lean process is active'
    pins=subprocess.run(wsl('/usr/bin/sha256sum',*PINS),capture_output=True,check=True)
    found=dict((x.split(maxsplit=1)[1].strip(),x.split()[0]) for x in pins.stdout.decode().splitlines())
    assert found==PINS
    runtime=json.loads((ROOT/'tmp/setup-20261015/runtime.json').read_text(encoding='utf-8'))
    job=ROOT/'tmp/current-s1r-M-20261018/phaseA1'
    job.mkdir(parents=True,exist_ok=False)
    lib=job/'lib';lib.mkdir()
    lib_linux=LINUX+'/'+lib.relative_to(ROOT).as_posix()
    lp=':'.join([lib_linux,LINUX+'/tmp/current-s1r-M-20261018/lib',DEPENDENCY_LIB,runtime['lean_path']])
    targets=['StructuralS1RM20261018/PhaseA1/QuantizedComponent','StructuralS1RM20261018/Sparse78']
    starts={}
    for target in targets:
        p=ROOT/(target+'.lean');starts[target]=sha(p)
        (job/(target.split('/')[-1]+'.lean')).write_bytes(p.read_bytes())
    save_new(job/'started.json',{'gate_sha256':ns.gate_sha256,'pid':os.getpid(),
        'source_sha256':starts,'started_unix':time.time(),'prefix_recompiled':False,
        'prefix_olean_sha256':prep['reused_prefix_olean_sha256']})
    passed=True
    for target in targets:
        name=target.split('/')[-1]
        output=lib/(target+'.olean');output.parent.mkdir(parents=True,exist_ok=True)
        assert not output.exists()
        log=job/(name+'.log');resources=job/(name+'.resources.log')
        args=wsl('/usr/bin/time','-v','-o',LINUX+'/'+resources.relative_to(ROOT).as_posix(),
            '/usr/bin/prlimit','--stack=268435456:268435456','--','env','LEAN_PATH='+lp,
            LEAN,'-j1','-M13500','--tstack=262144','-DrelaxedAutoImplicit=false',
            '-DElab.async=false','-R',LINUX,'-o',lib_linux+'/'+target+'.olean',LINUX+'/'+target+'.lean')
        save_new(job/(name+'.command.json'),{'argv':args})
        t0=time.time()
        with log.open('xb') as f:
            p=subprocess.Popen(args,stdout=f,stderr=subprocess.STDOUT)
            save_new(job/(name+'.child.json'),{'pid':p.pid,'start_unix':t0})
            print(json.dumps({'module':target,'child_pid':p.pid}),flush=True)
            code=p.wait();f.flush();os.fsync(f.fileno())
        unchanged=sha(ROOT/(target+'.lean'))==starts[target]
        result={'module':target,'exit_code':code,'elapsed_seconds':time.time()-t0,
            'source_sha256':starts[target],'source_unchanged':unchanged,
            'log_sha256':sha(log),'resource_sha256':sha(resources),
            'olean_sha256':sha(output) if output.exists() else None,
            'ordinary_compile_passed':code==0 and unchanged and output.exists(),
            'Nano_replayed':False,'global_cover_proved':False}
        save_new(job/(name+'.receipt.json'),result);print(json.dumps(result),flush=True)
        if not result['ordinary_compile_passed']:
            passed=False;break
    save_new(job/'terminal.json',{'passed':passed,'finished_unix':time.time()})
    return 0 if passed else 1


if __name__=='__main__':raise SystemExit(main())
