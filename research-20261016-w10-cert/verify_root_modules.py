"""Compile and bind the W10 initial-domain and finite-tree coverage lemmas."""
from pathlib import Path
import hashlib,json,re,subprocess,time

ROOT=Path(__file__).resolve().parents[1]; OUT=Path(__file__).parent
MODULES=['Coercivity','TreeCoverage','RootBounds']
BASE='/var/tmp/rh-zero-20261015'; LIB=BASE+'/w10-cert/lib'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    if not __debug__:raise RuntimeError('assertions required')
    runtime=json.loads((ROOT/'verification/gram-defect-20261015/setup/runtime.json').read_text())
    lp=LIB+':'+BASE+'/research-20261016/lib:'+BASE+'/record-verification/modular/lib:'+runtime['lean_path']
    compiler=runtime['lean']; prefix=['wsl.exe','--distribution','Ubuntu','--exec']
    src='/mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization'
    bound={str(ROOT/'StructuralW10Cert20261016'/f'{m}.lean'):sha(ROOT/'StructuralW10Cert20261016'/f'{m}.lean') for m in MODULES}
    bound[str(ROOT/'StructuralW10Cert20261016/LocalChecker.lean')]=sha(ROOT/'StructuralW10Cert20261016/LocalChecker.lean')
    records=[];start=time.time()
    for m in MODULES:
        command=prefix+['env','LEAN_PATH='+lp,compiler,'-j1','--tstack=32768','-DrelaxedAutoImplicit=false',
            '-R',src,'-o',LIB+'/StructuralW10Cert20261016/'+m+'.olean',src+'/StructuralW10Cert20261016/'+m+'.lean']
        t=time.time();r=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (OUT/('root-'+m+'.log')).write_bytes(r.stdout)
        print(m,'exit',r.returncode,'seconds',time.time()-t,flush=True)
        if r.returncode:
            print(r.stdout.decode('utf8',errors='replace'),flush=True);raise SystemExit(r.returncode)
        records.append({'module':'StructuralW10Cert20261016.'+m,'command':command,'exit_code':0,
            'source_sha256':bound[str(ROOT/'StructuralW10Cert20261016'/f'{m}.lean')],'seconds':time.time()-t})
    names=['Coercivity.pressure_le_energy','Coercivity.coordinate_bound','Coercivity.span_bound',
           'TreeCoverage.walk_sound','RootBounds.counterexample_in_root']
    audit=''.join('import StructuralW10Cert20261016.'+m+'\n' for m in MODULES)+''.join(
        '#print axioms StructuralW10Cert20261016.'+n+'\n' for n in names)
    (OUT/'RootAudit.lean').write_text(audit,encoding='utf8')
    cmd=prefix+['env','LEAN_PATH='+lp,compiler,'-j1','--tstack=32768','-DrelaxedAutoImplicit=false',
                src+'/research-20261016-w10-cert/RootAudit.lean']
    r=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (OUT/'root-axioms.log').write_bytes(r.stdout);text=r.stdout.decode('utf8',errors='replace')
    assert r.returncode==0,text
    allowed={'propext','Classical.choice','Quot.sound'};axioms={}
    for name in names:
        n='StructuralW10Cert20261016.'+name
        hit=re.search(re.escape("'"+n+"'")+r' depends on axioms: \[([^\]]*)\]',text,re.S)
        assert hit,(n,text)
        deps={x.strip() for x in hit.group(1).split(',') if x.strip()};assert deps<=allowed
        axioms[n]=sorted(deps)
    assert all(sha(p)==v for p,v in bound.items())
    result={'passed':True,'scope':'Initial coercive domain and generic finite-tree coverage only; no completed W10 floor',
            'modules':records,'bound_inputs_sha256':bound,'axioms':axioms,'seconds':time.time()-start}
    (OUT/'root-modules-verification.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'passed':True,'modules':len(records),'seconds':result['seconds']}),flush=True)
if __name__=='__main__':main()
