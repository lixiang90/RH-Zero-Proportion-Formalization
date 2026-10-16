"""Seal verified local research without claiming a complete analytic cover."""
from pathlib import Path
import hashlib,json,subprocess
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    assert __debug__
    summary=ROOT/'research-unconditional-20261016/verified-module-summary.json'
    modules=json.loads(summary.read_bytes())['modules'];bound={}
    for name,item in modules.items():
        source=ROOT/(name.replace('.','/')+'.lean')
        assert item['ordinary_lean_passed'] and item['current_log_matches_receipt']
        assert sha(source)==item['source_sha256']
        bound[str(source.relative_to(ROOT)).replace('\\','/')]=sha(source)
        receipt=ROOT/item['receipt'];r=json.loads(receipt.read_bytes())
        actual=next(x for x in r['modules'] if x['module']==name)
        assert actual['passed'] and actual['source_unchanged'] and actual['source_sha256']==sha(source)
        assert sha(receipt.parent/actual['log'])==actual['log_sha256']
        bound[item['receipt']]=sha(receipt)
    for name in ['GenericFloor','QuadraticEnvelope','InheritedEnvelope','DiagonalPolynomial','BasinPolynomials']:
        assert 'StructuralW10Unconditional20261016.'+name in modules
    for name in ['analytic_gram_replay.json','analytic_gram_wide_adaptive_replay.json']:
        receipt=HERE/name;r=json.loads(receipt.read_bytes())
        assert r['passed'] and r['all_inputs_unchanged']
        assert r['initial_sha256']==r['final_sha256']
        assert r['exact_chambers_checked']==r['candidate_floor_pass_count']==69
        for p,h in r['initial_sha256'].items():assert sha(ROOT/p)==h
        bound[str(receipt.relative_to(ROOT)).replace('\\','/')]=sha(receipt)
    generated=json.loads((HERE/'basin-polynomials-generated.json').read_bytes())
    assert generated['output_sha256']==sha(ROOT/'StructuralW10Unconditional20261016/BasinPolynomials.lean')
    assert generated['input_sha256']==sha(HERE/'analytic_gram_minorant.json')
    assert generated['script_sha256']==sha(HERE/'emit_basin_polynomials.py')
    hybrid=json.loads((HERE/'hybrid-pilot-summary.json').read_bytes())
    for run in hybrid['runs']:assert sha(HERE/run['path'])==run['sha256']
    status={'scope':__doc__,'ordinary_lean_verified_modules':len(modules),
        'algebraic_basin_bounds_lean_verified':69,'narrow_rational_chambers_independently_replayed':69,
        'wide_rational_chambers_independently_replayed':69,
        'all_scalar_PT_minorant_instances_lean_proven':False,
        'complete_global_floor_proven':False,'higher_kappa_proven':False,'upload_ready':False,
        'submitted':False,'global_hybrid_cover_complete':False,
        'candidate_parameter_sha256':sha(ROOT/'research-20261016/spectral-w10-refined-rational.json'),
        'verified_module_summary_sha256':sha(summary),'bound_current_inputs':bound,
        'remaining':['Concrete scalar PT/quadratic instances in Lean','A complete global cover or phase-concentration theorem',
                     'A size-compliant unconditional standalone source and exact-statement dual-kernel replay']}
    (HERE/'checkpoint.json').write_text(json.dumps(status,indent=2)+'\n',encoding='utf8')
    files={'.gitattributes','README.md'}
    for directory in ['StructuralW10Unconditional20261016','research-20261016-w10-unconditional','research-unconditional-20261016']:
        files.update(str(p.relative_to(ROOT)).replace('\\','/') for p in (ROOT/directory).rglob('*') if p.is_file() and p.suffix in ['.lean','.py','.json','.md','.log'])
    subprocess.run(['git','add','--force','--',*sorted(files)],cwd=ROOT,check=True)
    changed=subprocess.check_output(['git','diff','--cached','--name-only','-z'],cwd=ROOT).decode().split('\0')[:-1]
    entries=[]
    for p in changed:
        raw=subprocess.check_output(['git','show',':'+p],cwd=ROOT)
        try:raw.decode('utf8');binary=b'\0' in raw
        except UnicodeDecodeError:binary=True
        entries.append({'path':p,'sha':subprocess.check_output(['git','rev-parse',':'+p],cwd=ROOT).decode().strip(),'bytes':len(raw),'binary':binary})
    result={'parent':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip(),
        'tree':subprocess.check_output(['git','write-tree'],cwd=ROOT).decode().strip(),'entries':entries}
    out=ROOT/'tmp/w11-sync';out.mkdir(exist_ok=True,parents=True)
    (out/'staged.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'parent':result['parent'],'tree':result['tree'],'files':len(entries),'bytes':sum(r['bytes'] for r in entries),'global_floor_proven':False}))

if __name__=='__main__':main()
