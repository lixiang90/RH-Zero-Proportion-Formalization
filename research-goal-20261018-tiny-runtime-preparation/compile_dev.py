"""One gated serial Tiny development compile; no dependency recompilation."""
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
import traceback

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent
LINUX='/mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization'
JOB=ROOT/'tmp/current-s1r-tiny-20261018/dev-v0'
ALLOWED={'propext','Classical.choice','Quot.sound'}


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
    ns=ap.parse_args();gp=ROOT/ns.gate
    assert sha(gp)==ns.gate_sha256
    gate=json.loads(gp.read_text(encoding='utf-8'))
    prepared=HERE/'compiler-prepared.json'
    assert gate['authorized'] is True and gate['task']=='tiny-current-s1R-dev-ordinary-v0'
    assert gate['prepared_manifest_sha256']==sha(prepared)
    assert gate['automatic_repairs_or_retries']==0
    assert gate['recompile_passed_prefix'] is False
    prep=json.loads(prepared.read_text(encoding='utf-8'))
    assert gate['allowed_modules']==[x['module'] for x in prep['targets']]
    for row in prep['files']+prep['dependencies']:
        assert sha(ROOT/row['path'])==row['sha256'],row['path']
    assert Path(sys.executable).resolve()==Path(prep['Python_executable']['path']).resolve()
    assert sha(sys.executable)==prep['Python_executable']['sha256']
    ps=subprocess.run(wsl('/usr/bin/pgrep','-a','-x','lean'),capture_output=True)
    assert ps.returncode==1 and not ps.stdout,'another Lean process is active'
    external=prep['external_Linux_pins']
    h=subprocess.run(wsl('/usr/bin/sha256sum',*external),capture_output=True,check=True)
    got=dict((x.split(maxsplit=1)[1].strip(),x.split()[0]) for x in h.stdout.decode().splitlines())
    assert got==external
    runtime=json.loads((ROOT/'tmp/setup-20261015/runtime.json').read_text(encoding='utf-8'))
    JOB.mkdir(parents=True,exist_ok=False)
    try:
        lib=JOB/'lib';lib.mkdir(exist_ok=False)
        reused=[]
        for row in prep['reused_oleans']:
            src=ROOT/row['path'];dst=lib/row['relative_module_path']
            assert sha(src)==row['sha256'];dst.parent.mkdir(parents=True,exist_ok=True)
            assert not dst.exists();shutil.copy2(src,dst);assert sha(dst)==row['sha256']
            reused.append({'source':row['path'],'copy':dst.relative_to(ROOT).as_posix(),'sha256':sha(dst)})
        liblinux=LINUX+'/'+lib.relative_to(ROOT).as_posix()
        leanpath=':'.join([liblinux,'/var/tmp/rh-zero-20261015/record-verification/modular/lib',runtime['lean_path']])
        starts={t['module']:sha(ROOT/(t['module']+'.lean')) for t in prep['targets']}
        for t in prep['targets']:
            (JOB/(t['module'].split('/')[-1]+'.lean')).write_bytes((ROOT/(t['module']+'.lean')).read_bytes())
        write(JOB/'started.json',{'gate_sha256':ns.gate_sha256,'pid':os.getpid(),'source_sha256':starts,
            'start_unix':time.time(),'prefix_recompiled':False,'reused_oleans':reused,
            'automatic_repairs_or_retries':0,'report_points_only':{'seconds_per_module':1200,'log_bytes':20000000}})
        passed=True;receipts=[]
        for target in prep['targets']:
            module=target['module'];name=module.split('/')[-1]
            output=lib/(module+'.olean');output.parent.mkdir(parents=True,exist_ok=True)
            assert not output.exists();log=JOB/(name+'.log');resource=JOB/(name+'.resources.log')
            args=wsl('/usr/bin/time','-v','-o',LINUX+'/'+resource.relative_to(ROOT).as_posix(),
                '/usr/bin/prlimit','--stack=268435456:268435456','--','env','LEAN_PATH='+leanpath,
                runtime['lean'],'-j1','-M13500','--tstack=262144','-DrelaxedAutoImplicit=false',
                '-DElab.async=false','-R',LINUX,'-o',liblinux+'/'+module+'.olean',LINUX+'/'+module+'.lean')
            write(JOB/(name+'.command.json'),{'argv':args});t0=time.time()
            with log.open('xb') as f:
                child=subprocess.Popen(args,stdout=f,stderr=subprocess.STDOUT)
                write(JOB/(name+'.child.json'),{'pid':child.pid,'start_unix':t0})
                print(json.dumps({'module':module,'child_pid':child.pid}),flush=True)
                code=child.wait();f.flush();os.fsync(f.fileno())
            text=log.read_bytes().decode('utf-8',errors='replace')
            axioms=[]
            for theorem,raw in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S):
                axioms.append({'root':theorem,'axioms':[x.strip() for x in raw.split(',') if x.strip()]})
            expected=target['expected_printed_roots']
            audit=(len(axioms)==len(expected) and {x['root'] for x in axioms}==set(expected)
                and all(set(x['axioms'])<=ALLOWED for x in axioms)) if expected else None
            unchanged=sha(ROOT/(module+'.lean'))==starts[module]
            ordinary=code==0 and unchanged and output.exists()
            result={'module':module,'exit_code':code,'elapsed_seconds':time.time()-t0,
                'source_sha256':starts[module],'source_unchanged':unchanged,
                'log_sha256':sha(log),'resource_sha256':sha(resource),'printed_roots':axioms,
                'expected_printed_roots':expected,'olean_sha256':sha(output) if output.exists() else None,
                'ordinary_compile_passed':ordinary,'axiom_audit_passed':audit,
                'axiom_audit_deferred_to_Final_transitive_roots':not expected,
                'Nano_replayed':False,'official_Comparator_passed':False,'website_submission_ready':False}
            write(JOB/(name+'.receipt.json'),result);receipts.append(result)
            print(json.dumps({'module':module,'exit_code':code,'elapsed_seconds':result['elapsed_seconds'],
                'ordinary_compile_passed':ordinary,'axiom_audit_passed':audit,
                'source_sha256':starts[module],'olean_sha256':result['olean_sha256']}),flush=True)
            if not ordinary or (expected and not audit):passed=False;break
        write(JOB/'terminal.json',{'passed':passed,'finished_unix':time.time(),
            'completed_modules':len(receipts),'all_four_modules_completed':len(receipts)==4,
            'prefix_recompiled':False,'all_required_transitive_axiom_roots_audited':
                passed and len(receipts)==4 and receipts[-1]['axiom_audit_passed'] is True,
            'Nano_replayed':False,'trusted_tiny_CandidateSpec_prepared':False,
            'official_Comparator_passed':False,'website_submission_ready':False})
        return 0 if passed else 1
    except BaseException as e:
        failure={'type':type(e).__name__,'message':str(e),'traceback':traceback.format_exc(),'time_unix':time.time()}
        if not (JOB/'failed.json').exists():write(JOB/'failed.json',failure)
        if not (JOB/'terminal.json').exists():write(JOB/'terminal.json',{'passed':False,'runtime_exception':True,**failure})
        raise


if __name__=='__main__':raise SystemExit(main())
