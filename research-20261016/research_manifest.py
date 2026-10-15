"""Bind research sources to their successful ordinary-Lean receipts.

This checks existing receipts and hashes; it does not run Lean or nanoda.
The new numerical candidates have no completed unconditional theorem.
"""
from pathlib import Path
import hashlib, json

ROOT=Path(__file__).resolve().parents[1]
BASE=Path(__file__).parent
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    if not __debug__:raise RuntimeError('Do not run with -O: audit assertions are required')
    modules={};receipts=[];permitted={'propext','Classical.choice','Quot.sound'}
    for name in ['window-structural-verification.json','window-coboundary-counting-verification.json',
                 'window-affine-flow-verification.json','window-tangent-support-verification.json']:
        path=BASE/name;r=json.loads(path.read_text());assert r['passed'] and r['inputs_unchanged']
        for mod in r['compiled_modules']:
            source=ROOT/(mod['module'].replace('.','/')+'.lean')
            assert mod['exit_code']==0 and digest(source)==mod['source_sha256']
            modules[str(source.relative_to(ROOT))]=digest(source)
        for deps in r['axioms'].values():assert set(deps)<=permitted
        for source,expected in r['bound_inputs_sha256'].items():assert digest(Path(source))==expected
        receipts.append({'path':str(path.relative_to(ROOT)),'sha256':digest(path)})
    for name in ['potential-range-canonical-compile.json','generic-cover-compile.json']:
        path=BASE/name;r=json.loads(path.read_text());source=Path(r['source_path'])
        if not source.is_absolute():source=ROOT/source
        assert r['passed'] and r['exit_code']==0 and digest(source)==r['source_sha256']
        assert 'sorryAx' not in r['stdout']
        modules[str(source.relative_to(ROOT))]=digest(source)
        receipts.append({'path':str(path.relative_to(ROOT)),'sha256':digest(path)})
    for name in ['spectral-w10-compile.json','spectral-w10-refined-compile.json']:
        path=BASE/name;r=json.loads(path.read_text());source=ROOT/r['source']
        assert r['status']=='PASSED' and r['exit_code']==0
        assert digest(source)==r['source_sha256']==r['source_after_sha256']
        assert 'sorryAx' not in r['stdout']
        modules[str(source.relative_to(ROOT))]=digest(source)
        receipts.append({'path':str(path.relative_to(ROOT)),'sha256':digest(path)})
    assert set(modules)=={str(p.relative_to(ROOT)) for p in (ROOT/'StructuralResearch20261016').glob('*.lean')}
    frozen={
      'GramDefect20261015/Core.lean':'2062b1f9540e1ea7b78d382f46a234780dcda03f4e3a6c21467c84b611505ff5',
      'GramDefect20261015/SharpWindow.lean':'830514965ca5cb26a19be2b216fbedd37744b7c66e862c46bf697b9e29d7c49f',
      'GramDefect20261015/RefinedCounting.lean':'e756b01819f5063e1c9dba906b75e12c036e384156ff5734f566c2ea7c5d70cf',
      'GramDefect20261015/Final.lean':'029f2a0e8d8c5f18908a265bb9e21a5e543d57dafd7f71fe4e14187ff85b4561',
      'submission/gram-defect-20261015/proof/Solution.lean':'0883ee87e8f6b0284715d4e5d8b1e295801dfeeb8d7970a2554500fb49ed9f0b'}
    for path,expected in frozen.items():assert digest(ROOT/path)==expected
    result={'scope':'research source/receipt binding audit; no new unconditional score',
            'passed':True,'ordinary_Lean_modules':modules,'receipts':receipts,
            'frozen_proof_inputs_unchanged':frozen,
            'new_full_statement_comparison':False,'new_independent_nanoda_replay':False,
            'new_unconditional_zero_proportion_proved':False}
    (BASE/'source-verification-manifest.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'passed':True,'modules':len(modules),'receipts':len(receipts),
                      'frozen_proof_inputs_unchanged':len(frozen)}))

if __name__=='__main__':main()
