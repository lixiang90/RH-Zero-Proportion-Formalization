"""Only two gated current-profile analytic bridge modules; no finite case data."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent
LINUX='/mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization'


def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):h.update(block)
    return h.hexdigest()


def write(p,x):
    with Path(p).open('x',encoding='utf-8',newline='\n') as f:
        json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())


def wsl(*args):return ['wsl.exe','--distribution','Ubuntu','--exec',*args]


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--gate',required=True);ap.add_argument('--gate-sha256',required=True)
    ns=ap.parse_args();gatepath=ROOT/ns.gate
    assert sha(gatepath)==ns.gate_sha256
    gate=json.loads(gatepath.read_text(encoding='utf-8'))
    prepared=HERE/'phaseO1-prepared.json'
    assert gate['authorized'] is True and gate['task']=='stageO-current-s1R-strong-bridge-v1'
    assert gate['prepared_manifest_sha256']==sha(prepared)
    assert gate['fixed_case_data_or_Sparse_or_B2_authorized'] is False
    assert gate['automatic_repairs_or_retries']==0
    prep=json.loads(prepared.read_text(encoding='utf-8'))
    for row in prep['files']+prep['dependencies']:
        assert sha(ROOT/row['path'])==row['sha256'],row['path']
    assert Path(sys.executable).resolve()==Path(prep['Python_executable']['path']).resolve()
    assert sha(sys.executable)==prep['Python_executable']['sha256']
    ps=subprocess.run(wsl('/usr/bin/pgrep','-a','-x','lean'),capture_output=True)
    assert ps.returncode==1 and not ps.stdout,'another Lean process is active'
    external=prep['external_Linux_pins']
    h=subprocess.run(wsl('/usr/bin/sha256sum',*external),capture_output=True,check=True)
    assert dict((x.split(maxsplit=1)[1].strip(),x.split()[0]) for x in h.stdout.decode().splitlines())==external
    runtime=json.loads((ROOT/'tmp/setup-20261015/runtime.json').read_text(encoding='utf-8'))
    job=ROOT/'tmp/current-s1r-O-20261018/phaseO1';job.mkdir(parents=True,exist_ok=False)
    lib=job/'lib';lib.mkdir(parents=True,exist_ok=False)
    for row in prep['reused_oleans']:
        src=ROOT/row['path'];dst=lib/row['relative_module_path']
        assert sha(src)==row['sha256'];dst.parent.mkdir(parents=True,exist_ok=True)
        assert not dst.exists();shutil.copy2(src,dst);assert sha(dst)==row['sha256']
    liblinux=LINUX+'/'+lib.relative_to(ROOT).as_posix()
    path=':'.join([liblinux,'/var/tmp/rh-zero-20261015/record-verification/modular/lib',runtime['lean_path']])
    targets=['StructuralS1RO20261018/PhaseO1/StrongQuantized']
    starts={name:sha(ROOT/(name+'.lean')) for name in targets}
    for name in targets:(job/(name.split('/')[-1]+'.lean')).write_bytes((ROOT/(name+'.lean')).read_bytes())
    write(job/'started.json',{'gate_sha256':ns.gate_sha256,'pid':os.getpid(),'source_sha256':starts,
        'start_unix':time.time(),'prefix_recompiled':False,'finite_data_or_Sparse_or_B2_runs':0})
    passed=True
    for target in targets:
        name=target.split('/')[-1];output=lib/(target+'.olean');output.parent.mkdir(parents=True,exist_ok=True)
        assert not output.exists();log=job/(name+'.log');resource=job/(name+'.resources.log')
        args=wsl('/usr/bin/time','-v','-o',LINUX+'/'+resource.relative_to(ROOT).as_posix(),
            '/usr/bin/prlimit','--stack=268435456:268435456','--','env','LEAN_PATH='+path,
            runtime['lean'],'-j1','-M13500','--tstack=262144','-DrelaxedAutoImplicit=false',
            '-DElab.async=false','-R',LINUX,'-o',liblinux+'/'+target+'.olean',LINUX+'/'+target+'.lean')
        write(job/(name+'.command.json'),{'argv':args});t0=time.time()
        with log.open('xb') as f:
            child=subprocess.Popen(args,stdout=f,stderr=subprocess.STDOUT)
            write(job/(name+'.child.json'),{'pid':child.pid,'start_unix':t0})
            print(json.dumps({'module':target,'child_pid':child.pid}),flush=True)
            code=child.wait();f.flush();os.fsync(f.fileno())
        text=log.read_bytes().decode('utf-8',errors='replace')
        axioms=[]
        for theorem,raw in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S):
            aa=[x.strip() for x in raw.split(',') if x.strip()]
            axioms.append({'root':theorem,'axioms':aa})
        audit=bool(axioms) and all(set(x['axioms'])<= {'propext','Classical.choice','Quot.sound'} for x in axioms)
        unchanged=sha(ROOT/(target+'.lean'))==starts[target]
        result={'module':target,'exit_code':code,'elapsed_seconds':time.time()-t0,
            'source_sha256':starts[target],'source_unchanged':unchanged,
            'log_sha256':sha(log),'resource_sha256':sha(resource),'printed_roots':axioms,
            'olean_sha256':sha(output) if output.exists() else None,
            'ordinary_compile_passed':code==0 and unchanged and output.exists(),
            'axiom_audit_passed':audit,'Nano_replayed':False,'fixed_pair_floor_proved':False,'global_floor_proved':False}
        write(job/(name+'.receipt.json'),result);print(json.dumps(result),flush=True)
        if not result['ordinary_compile_passed'] or not audit:passed=False;break
    write(job/'terminal.json',{'passed':passed,'finished_unix':time.time()})
    return 0 if passed else 1


if __name__=='__main__':raise SystemExit(main())
