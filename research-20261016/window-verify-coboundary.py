"""Compile the independent coboundary lemmas and inspect their exact axioms.

Uses the pinned 2026-10-15 runtime and its previously verified Core olean.
This checks the new modules with ordinary Lean only: no larger kappa, website
acceptance, full-environment kernel replay, or independent nanoda claim is made.
"""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, subprocess, time

ROOT = Path(__file__).resolve().parents[1]
MODULES = ['StructuralResearch20261016.Coboundary']
THEOREMS = [
    'StructuralResearch20261016.Coboundary.sum_lower_of_local',
    'StructuralResearch20261016.Coboundary.sum_lower_of_bounded_local',
    'StructuralResearch20261016.Coboundary.sum_lower_of_periodic_local',
    'StructuralResearch20261016.Coboundary.absorb_boundary',
    'StructuralResearch20261016.Coboundary.boundary_budget_of_threshold',
    'StructuralResearch20261016.Coboundary.absorb_boundary_of_threshold',
    'StructuralResearch20261016.Coboundary.head_window',
    'StructuralResearch20261016.Coboundary.tail_window',
    'StructuralResearch20261016.Coboundary.summed_of_coboundary',
    'StructuralResearch20261016.Coboundary.summed_of_separated_coboundary',
    'StructuralResearch20261016.Coboundary.summed_of_pointwise',
    'StructuralResearch20261016.Coboundary.block_energy_band_of_sum',
    'StructuralResearch20261016.Coboundary.block_energy_band_summed',
    'StructuralResearch20261016.Coboundary.sorted_separated',
    'StructuralResearch20261016.Coboundary.block_energy_band_separated',
    'StructuralResearch20261016.Coboundary.remainder_bound_summed',
    'StructuralResearch20261016.Coboundary.remainder_bound_coboundary',
    'StructuralResearch20261016.Coboundary.remainder_bound_separated_summed',
    'StructuralResearch20261016.Coboundary.remainder_bound_separated_coboundary',
    'StructuralResearch20261016.Coboundary.block_remainder_bound_summed',
]
ALLOWED = {'propext', 'Quot.sound', 'Classical.choice'}

def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024*1024), b''): h.update(block)
    return h.hexdigest()

def linux_path(path):
    path=Path(path).resolve()
    if os.name!='nt': return str(path)
    assert len(path.drive)==2 and path.drive[1]==':', path
    return '/mnt/'+path.drive[0].lower()+path.as_posix()[2:]

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runtime',type=Path,default=ROOT/'verification/gram-defect-20261015/setup/runtime.json')
    parser.add_argument('--base-receipt',type=Path,default=ROOT/'verification/gram-defect-20261015/lean/modular/verification.json')
    args=parser.parse_args()
    runtime=json.loads(args.runtime.read_text(encoding='utf8'))
    base=json.loads(args.base_receipt.read_text(encoding='utf8'))
    assert base['local_modular_verified'] and base['inputs_unchanged']
    stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    out=ROOT/'research-20261016'/('window-coboundary-check-'+stamp)
    out.mkdir()
    work=runtime['runtime_root']+'/research-20261016/coboundary-check-'+stamp
    prefix=['wsl.exe','--distribution','Ubuntu','--exec'] if os.name=='nt' else []
    def call(argv,log=None):
        start=time.monotonic()
        result=subprocess.run(prefix+argv,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        if log: Path(log).write_bytes(result.stdout)
        assert result.returncode==0, (argv,result.returncode,result.stdout.decode('utf8',errors='replace'))
        return result.stdout,time.monotonic()-start
    def remote_sha(path):
        raw,_=call(['sha256sum',path])
        matches=re.findall(rb'(?<![0-9a-f])([0-9a-f]{64})  ',raw)
        assert len(matches)==1,(path,raw)
        return matches[0].decode('ascii')
    assert remote_sha(runtime['lean'])==runtime['lean_sha256']
    cached=runtime['runtime_root']+'/record-verification/modular/lib'
    core_record=next(r for r in base['compiled_modules'] if r['module']=='GramDefect20261015.Core')
    assert remote_sha(core_record['olean'])==core_record['olean_sha256']
    assert sha(ROOT/'GramDefect20261015/Core.lean')==core_record['source_sha256']
    bound={str(ROOT/(m.replace('.','/')+'.lean')):sha(ROOT/(m.replace('.','/')+'.lean')) for m in MODULES}
    bound[str(args.runtime.resolve())]=sha(args.runtime)
    bound[str(args.base_receipt.resolve())]=sha(args.base_receipt)
    bound[str(Path(__file__).resolve())]=sha(__file__)
    audit='\n'.join('import '+m for m in MODULES)+'\n\n'+''.join('#print axioms '+n+'\n' for n in THEOREMS)
    auditfile=out/'Audit.lean';auditfile.write_text(audit,encoding='utf8')
    call(['mkdir','-p',work+'/source/StructuralResearch20261016',work+'/lib/StructuralResearch20261016'])
    for module in MODULES:
        rel=module.replace('.','/')+'.lean'
        call(['cp',linux_path(ROOT/rel),work+'/source/'+rel])
        assert remote_sha(work+'/source/'+rel)==bound[str(ROOT/rel)]
    call(['cp',linux_path(auditfile),work+'/source/Audit.lean'])
    lp=work+'/lib:'+cached+':'+runtime['lean_path']
    command=['env','LEAN_PATH='+lp,runtime['lean'],'-j1','--tstack=32768','-DrelaxedAutoImplicit=false','-R',work+'/source']
    records=[]
    for module in MODULES:
        rel=module.replace('.','/')
        argv=command+['-o',work+'/lib/'+rel+'.olean',work+'/source/'+rel+'.lean']
        logfile=out/(module+'.log')
        _,elapsed=call(argv,logfile)
        records.append({'module':module,'command':prefix+argv,'exit_code':0,
            'seconds':elapsed,'source_sha256':bound[str(ROOT/(rel+'.lean'))],
            'olean':work+'/lib/'+rel+'.olean','olean_sha256':remote_sha(work+'/lib/'+rel+'.olean'),
            'log':str(logfile.relative_to(ROOT)),'log_sha256':sha(logfile)})
        print(module+' compiled',flush=True)
    raw,elapsed=call(command+[work+'/source/Audit.lean'],out/'axioms.log')
    text=raw.decode('utf8',errors='replace')
    axioms={}
    for theorem in THEOREMS:
        pattern=re.escape("'"+theorem+"'")+r' depends on axioms: \[([^\]]*)\]'
        hit=re.search(pattern,text,re.S)
        if hit: observed={a.strip() for a in hit.group(1).split(',') if a.strip()}
        else:
            assert "'"+theorem+"' does not depend on any axioms" in text, (theorem,text)
            observed=set()
        assert observed<=ALLOWED,(theorem,observed)
        axioms[theorem]=sorted(observed)
    assert all(sha(path)==digest for path,digest in bound.items())
    assert remote_sha(core_record['olean'])==core_record['olean_sha256']
    report={'scope':'Independent finite coboundary and summed-certificate payment lemmas only; ordinary Lean and axiom inspection using previously verified cached Core. No improved kappa or website acceptance claim.',
        'passed':True,'utc':stamp,'compiler':runtime['lean'],'compiler_sha256':runtime['lean_sha256'],
        'bound_inputs_sha256':bound,'cached_Core_olean_sha256':core_record['olean_sha256'],
        'compiled_modules':records,'axioms':axioms,'permitted_axioms':sorted(ALLOWED),
        'axiom_audit_seconds':elapsed,'axiom_log':str((out/'axioms.log').relative_to(ROOT)),
        'axiom_log_sha256':sha(out/'axioms.log'),'generated_audit_source_sha256':sha(auditfile),
        'inputs_unchanged':True,'independent_nanoda_run':False,'full_environment_kernel_replay_run':False}
    target=ROOT/'research-20261016/window-coboundary-verification.json'
    target.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
    print(str(target),flush=True)

if __name__=='__main__': main()
