"""Serial durable default-kernel verifier; the complete manifest is the target.

The verifier never treats an external arithmetic audit as a theorem. Resume is
allowed only for source-hash matched successful modules with the saved olean.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, subprocess, time

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent
LIB='/var/tmp/rh-zero-20261015/w10-cert/lib'
LINUX='/mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization'

def sha(raw):return hashlib.sha256(raw).hexdigest()
def save(path,value):
    temp=path.with_suffix('.tmp')
    temp.write_text(json.dumps(value,indent=2)+'\n',encoding='utf8')
    temp.replace(path)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('modules',nargs='*')
    ap.add_argument('--complete',action='store_true')
    ap.add_argument('--bundled',action='store_true')
    ap.add_argument('--keep-going',action='store_true',help='Keep serving independent requested modules after an error; failed modules remain failed.')
    ap.add_argument('--receipt',default='lean_verification.json')
    args=ap.parse_args()
    runtime=json.loads((ROOT/'tmp/setup-20261015/runtime.json').read_text())
    leanpath=':'.join([LIB,'/var/tmp/rh-zero-20261015/research-20261016/lib','/var/tmp/rh-zero-20261015/record-verification/modular/lib',runtime['lean_path']])
    pre=['wsl.exe','--distribution','Ubuntu','--exec']
    compiler=subprocess.run(pre+['/usr/bin/sha256sum',runtime['lean']],capture_output=True,check=True).stdout.decode().split()[0]
    assert compiler==runtime['lean_sha256']
    manifest=json.loads((HERE/'lean_manifest.json').read_text())
    global_modules=[r['module'] for r in manifest['modules']]
    if args.bundled:
        assert args.complete
        bundled=json.loads((HERE/'lean_bundle_manifest.json').read_text())
        assert bundled.get('composition_uses_bundles')
        assert bundled['partition_manifest_sha256']==sha((HERE/'lean_manifest.json').read_bytes())
        global_modules=[r['module'] for r in bundled['bundles']]
    targets=list(args.modules)
    if args.complete:
        targets+=['StructuralGoal20261016.LeanCoverBase']+global_modules+['StructuralGoal20261016.LeanCoverComplete','StructuralGoal20261016.LeanCoverConclusion']
    assert targets
    receipt=HERE/args.receipt
    if receipt.exists():
        record=json.loads(receipt.read_text())
        assert record['compiler_sha256']==compiler
        current_driver=sha(Path(__file__).read_bytes())
        if record['driver_sha256']!=current_driver:
            record.setdefault('prior_driver_sha256',[]).append(record['driver_sha256'])
            record['driver_sha256']=current_driver
    else:
        record={'scope':'Actual ordinary-kernel compilation. Full global theorem exists only once every listed part and LeanCoverComplete pass with current source hashes.','driver_sha256':sha(Path(__file__).read_bytes()),'compiler_sha256':compiler,'modules':[],'passed':False,'complete_lean_proven':False}
    known={r['module']:r for r in record['modules']}
    statuspath=HERE/'lean_live_status.json'
    index=0
    while True:
        urgent_path=HERE/'lean_priority_queue.json'
        if urgent_path.exists():
            urgent=json.loads(urgent_path.read_text(encoding='utf8'))
            assert isinstance(urgent,list) and all(isinstance(m,str) for m in urgent)
            if urgent:
                save(urgent_path,[])
                urgent=list(dict.fromkeys(urgent))
                targets[index:]=urgent+[m for m in targets[index:] if m not in urgent]
        if index>=len(targets):
            break
        module=targets[index]
        index+=1
        assert re.fullmatch(r'[A-Za-z0-9_]+(\.[A-Za-z0-9_]+)+',module)
        relative=module.replace('.','/')
        source=ROOT/(relative+'.lean')
        sourcehash=sha(source.read_bytes())
        outputolean=LIB+'/'+relative+'.olean'
        prior=known.get(module)
        if prior and prior['passed'] and prior['source_sha256']==sourcehash:
            cached=subprocess.run(pre+['/usr/bin/sha256sum',outputolean],capture_output=True)
            if cached.returncode==0 and cached.stdout.decode().split()[0]==prior['olean_sha256']:
                print(json.dumps({'resumed_verified_module':module}),flush=True)
                continue
        subprocess.run(pre+['/bin/mkdir','-p',LIB+'/'+relative.rsplit('/',1)[0]],check=True)
        argv=pre+['/usr/bin/prlimit','--stack=268435456:268435456','--','env','LEAN_PATH='+leanpath,runtime['lean'],'-j1','-M13500','--tstack=262144','-DrelaxedAutoImplicit=false','-R',LINUX,'-o',outputolean,LINUX+'/'+relative+'.lean']
        logname='lean_'+module.rsplit('.',1)[-1]+'_'+sourcehash[:12]+'.log'
        logpath=HERE/logname
        begin=time.time()
        with logpath.open('wb') as log:
            proc=subprocess.Popen(argv,stdout=log,stderr=subprocess.STDOUT)
            status={'driver_pid':os.getpid(),'wsl_process_pid':proc.pid,'module':module,'source_sha256':sourcehash,'index':index,'target_count':len(targets),'started_unix':begin,'live':True,'log':logname}
            save(statuspath,status)
            print(json.dumps(status),flush=True)
            exitcode=proc.wait()
        raw=logpath.read_bytes()
        result={'module':module,'source_sha256':sourcehash,'source_unchanged':sha(source.read_bytes())==sourcehash,'command':argv,'exit_code':exitcode,'whole_process_seconds':time.time()-begin,'log':logname,'log_sha256':sha(raw),'passed':exitcode==0 and b'sorryAx' not in raw and sha(source.read_bytes())==sourcehash,'synchronous_elaboration':'set_option Elab.async false' in source.read_text(encoding='utf8')}
        if result['passed']:
            result['olean_sha256']=subprocess.run(pre+['/usr/bin/sha256sum',outputolean],capture_output=True,check=True).stdout.decode().split()[0]
        known[module]=result
        record['modules']=list(known.values())
        record['passed']=all(known.get(m,{}).get('passed',False) for m in targets)
        complete=['StructuralGoal20261016.LeanCoverBase']+global_modules+['StructuralGoal20261016.LeanCoverComplete','StructuralGoal20261016.LeanCoverConclusion']
        record['complete_lean_proven']=all(known.get(m,{}).get('passed',False) for m in complete)
        save(receipt,record)
        status.update(live=False,exit_code=exitcode,finished_unix=time.time())
        save(statuspath,status)
        print(json.dumps({k:v for k,v in result.items() if k!='command'}),flush=True)
        if not result['passed']:
            # Full diagnostics stay in the hash-bound log. Repeated finite
            # expansions can otherwise flood a persistent job with megabytes.
            diagnostic=raw.decode('utf8',errors='replace')
            errors=[line for line in diagnostic.splitlines() if ': error' in line]
            if errors:
                print('\n'.join(errors[:30]),flush=True)
                if len(errors)>30:
                    print(json.dumps({'additional_errors_in_log':len(errors)-30}),flush=True)
            else:
                print(diagnostic[-12000:],flush=True)
            if (args.complete and module not in complete) or args.keep_going:
                print(json.dumps({'priority_failed_global_queue_continues':module}),flush=True)
                continue
            raise SystemExit(1)
    record['passed']=all(known.get(m,{}).get('passed',False) for m in targets)
    save(receipt,record)
    print(json.dumps({'finished':True,'complete_lean_proven':record['complete_lean_proven'],'passed':record['passed']}),flush=True)
    if not record['passed']:
        raise SystemExit(1)

if __name__=='__main__':main()
