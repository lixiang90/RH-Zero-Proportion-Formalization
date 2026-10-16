"""Compile the review/counting/coverage modules using frozen cached Core.

This is ordinary Lean elaboration and an axiom audit, not a complete higher
proportion proof, Comparator verification, or independent nanoda replay.
"""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, subprocess, time

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(__file__).resolve().parent
MODULES = ['StructuralW10Cert20261016.Reflection',
           'StructuralW10Cert20261016.FinalConditional',
           'StructuralW10Cert20261016.FloorTransfer',
           'StructuralW10Cert20261016.OrderCoverage',
           'StructuralW10Cert20261016.LeafDispatch']
ALLOWED = {'propext', 'Quot.sound', 'Classical.choice'}
THEOREMS = [
    'StructuralW10Cert20261016.Reflection.point_reverse',
    'StructuralW10Cert20261016.Reflection.Fw_reverse',
] + ['StructuralW10Cert20261016.FinalConditional.' + n for n in [
    'exact_formula', 'strict_improvement', 'separated_summed', 'simple_dyadic',
    'simple_cumulative', 'distinct_dyadic', 'distinct_cumulative']] + [
    'StructuralW10Cert20261016.FloorTransfer.'+n for n in
    ['separated_floor']] + [
    'StructuralW10Cert20261016.OrderCoverage.'+n for n in ['normalize_sound','walk_sound']
] + ['StructuralW10Cert20261016.LeafDispatch.check_sound']

def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def wslpath(path):
    path = Path(path).resolve()
    return '/mnt/' + path.drive[0].lower() + path.as_posix()[2:]

def main():
    if not __debug__: raise RuntimeError('Assertions must remain enabled for this verifier')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--metadata-only',action='store_true')
    parser.add_argument('--skip-metadata',action='store_true')
    args=parser.parse_args()
    runtime = json.loads((ROOT/'verification/gram-defect-20261015/setup/runtime.json').read_text())
    base = json.loads((ROOT/'verification/gram-defect-20261015/lean/modular/verification.json').read_text())
    counting = json.loads((ROOT/'research-20261016/window-coboundary-counting-verification.json').read_text())
    wc = json.loads((ROOT/'research-20261016/spectral-w10-refined-compile.json').read_text())
    root_modules = json.loads((OUT/'root-modules-verification.json').read_text())
    assert root_modules['passed']
    for p,digest in root_modules['bound_inputs_sha256'].items(): assert sha(p)==digest,p
    assert counting['passed'] and base['local_modular_verified'] and base['inputs_unchanged']
    for p, digest in counting['bound_inputs_sha256'].items(): assert sha(p) == digest, p
    assert sha(ROOT/wc['source']) == wc['source_sha256'] == wc['source_after_sha256']
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    work = runtime['runtime_root']+'/research-20261016-w10-cert/review-'+stamp
    out = OUT/('review-lean-'+stamp); out.mkdir()
    prefix = ['wsl.exe','--distribution','Ubuntu','--exec'] if os.name == 'nt' else []
    def call(args, log=None):
        start=time.monotonic()
        result=subprocess.run(prefix+args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        if log: Path(log).write_bytes(result.stdout)
        return result, time.monotonic()-start
    def remote_sha(path):
        result,_=call(['sha256sum',path]); assert result.returncode == 0
        hits=re.findall(rb'(?<![0-9a-f])([0-9a-f]{64})  ',result.stdout)
        assert len(hits)==1, (path,result.stdout)
        return hits[0].decode()
    assert remote_sha(runtime['lean'])==runtime['lean_sha256']
    for rec in base['compiled_modules']:
        if rec['module'] not in ['GramDefect20261015.Core',
                                  'GramDefect20261015.SharpWindow',
                                  'GramDefect20261015.RefinedCounting']:
            continue
        assert remote_sha(rec['olean']) == rec['olean_sha256']
        assert sha(ROOT/(rec['module'].replace('.','/')+'.lean')) == rec['source_sha256']
    for rec in counting['compiled_modules']:
        assert remote_sha(rec['olean'])==rec['olean_sha256']
        assert sha(ROOT/(rec['module'].replace('.','/')+'.lean'))==rec['source_sha256']
    call(['mkdir','-p',work+'/lib/StructuralW10Cert20261016',
          work+'/lib/StructuralResearch20261016'])
    root_olean=root_modules['modules'][0]['command']
    root_olean=root_olean[root_olean.index('-o')+1]
    root_lib=root_olean.split('/StructuralW10Cert20261016/')[0]
    result,_=call(['cp','-a',root_lib+'/StructuralW10Cert20261016/.',
                  work+'/lib/StructuralW10Cert20261016/'])
    assert result.returncode==0
    # Lean resolves a top-level module directory as one search-path root;
    # consolidate this namespace rather than relying on per-file fallback.
    for rec in counting['compiled_modules']:
        dest=work+'/lib/'+rec['module'].replace('.','/')+'.olean'
        result,_=call(['cp',rec['olean'],dest]); assert result.returncode==0
        assert remote_sha(dest)==rec['olean_sha256']
    wolean=wc['command'][wc['command'].index('-o')+1]
    wsha=remote_sha(wolean)
    wdest=work+'/lib/StructuralResearch20261016/W10RefinedCandidate.olean'
    result,_=call(['cp',wolean,wdest]); assert result.returncode==0
    assert remote_sha(wdest)==wsha
    lp=':'.join([work+'/lib',
        runtime['runtime_root']+'/record-verification/modular/lib', runtime['lean_path']])
    command=['env','LEAN_PATH='+lp,runtime['lean'],'-j1','--tstack=32768',
             '-DrelaxedAutoImplicit=false','-R',wslpath(ROOT)]
    if not args.skip_metadata:
        metadata_source=OUT/'UsedCore.lean'
        metadata_result,metadata_seconds=call(command+[wslpath(metadata_source)],out/'UsedCore.log')
        print('UsedCore metadata exit',metadata_result.returncode,flush=True)
        if metadata_result.returncode:
            print(metadata_result.stdout.decode('utf8',errors='replace')[:12000]);raise SystemExit(metadata_result.returncode)
        metadata_receipt={'passed':True,'scope':'Dependency metadata only, not a proof evaluation',
            'source_sha256':sha(metadata_source),'output_sha256':sha(OUT/'core-dependencies.json'),
            'seconds':metadata_seconds,'log':str((out/'UsedCore.log').relative_to(ROOT)),
            'compiler_sha256':runtime['lean_sha256']}
        (OUT/'core-dependencies-verification.json').write_text(json.dumps(metadata_receipt,indent=2)+'\n')
    if args.metadata_only: return
    records=[]; axioms={}; passed=True
    bound={m:sha(ROOT/(m.replace('.','/')+'.lean')) for m in MODULES}
    previous_path=OUT/'review-lean-verification.json'
    previous=json.loads(previous_path.read_text()) if previous_path.exists() else {}
    previous_records={r['module']:r for r in previous.get('modules',[]) if r['exit_code']==0}
    for module in MODULES:
        src=ROOT/(module.replace('.','/')+'.lean')
        olean=work+'/lib/'+module.replace('.','/')+'.olean'
        logfile=out/(module+'.log')
        argv=command+['-o',olean,wslpath(src)]
        reusable=previous_records.get(module)
        predecessors=MODULES[:MODULES.index(module)+1]
        if reusable and all(previous.get('source_sha256',{}).get(m)==bound[m] for m in predecessors):
            assert remote_sha(reusable['olean'])==reusable['olean_sha256']
            assert sha(ROOT/reusable['log'])==reusable['log_sha256']
            result,_=call(['cp',reusable['olean'],olean]);assert result.returncode==0
            assert remote_sha(olean)==reusable['olean_sha256']
            record={**reusable,'olean':olean,'reused_exact_verified_olean':True}
            records.append(record)
            text=(ROOT/reusable['log']).read_text(encoding='utf8',errors='replace')
            print(module,'reused verified unchanged source/olean',flush=True)
        else:
            result,elapsed=call(argv,logfile)
            records.append({'module':module,'command':prefix+argv,'exit_code':result.returncode,
                'seconds':elapsed,'source_sha256':bound[module],
                'olean':olean,'olean_sha256':remote_sha(olean) if result.returncode == 0 else None,
                'log':str(logfile.relative_to(ROOT)),'log_sha256':sha(logfile)})
            print(module, 'exit',result.returncode,flush=True)
            if result.returncode:
                print(result.stdout.decode('utf8',errors='replace')[:18000]); passed=False; break
            text=result.stdout.decode('utf8',errors='replace')
        for theorem in THEOREMS:
            hit=re.search(re.escape("'"+theorem+"'")+r' depends on axioms: \[([^\]]*)\]',text,re.S)
            if hit:
                observed={a.strip() for a in hit.group(1).split(',') if a.strip()}
                assert observed <= ALLOWED, (theorem,observed)
                axioms[theorem]=sorted(observed)
            elif ("'"+theorem+"' does not depend on any axioms") in text: axioms[theorem]=[]
    for module,digest in bound.items(): assert sha(ROOT/(module.replace('.','/')+'.lean'))==digest
    passed=passed and len(axioms)==len(THEOREMS)
    receipt={'scope':__doc__, 'passed':passed,'utc':stamp,
        'compiler_sha256':runtime['lean_sha256'],'modules':records,'axioms':axioms,
        'all_inputs_unchanged':True, 'source_sha256':bound,
        'conditional_only':True, 'higher_kappa_proven':False}
    (OUT/'review-lean-verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    assert passed

if __name__ == '__main__': main()
