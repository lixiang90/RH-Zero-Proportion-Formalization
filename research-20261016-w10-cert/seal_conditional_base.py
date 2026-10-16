"""Archive the exact compiled conditional base; never certify a website result."""
from pathlib import Path
import hashlib, json, shutil

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent
DEST=ROOT/'submission/w10-20261016'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    if not __debug__:raise RuntimeError('Archive assertions must remain enabled')
    verified=HERE/'compressed-preflight.json'
    decoded=HERE/'independent-source-decode-preflight.json'
    v=json.loads(verified.read_bytes());d=json.loads(decoded.read_bytes())
    source=HERE/'BundlePreflight.lean';readable=HERE/'ExpandedPreflight.lean'
    assert v['passed'] and v['exit_code']==0 and v['source_unchanged']
    assert v['source_sha256']==d['upload_sha256']==sha(source)
    assert d['passed'] and d['decoded_body_exact_readable_region']
    assert d['readable_sha256']==sha(readable)
    assert not v['all_partition_checked'] and not v['higher_kappa_proven']
    output=DEST/'proof/ConditionalBase.lean'
    expanded=DEST/'uncompressed/ExpandedConditionalBase.lean'
    output.parent.mkdir(parents=True,exist_ok=True)
    expanded.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(source,output);shutil.copyfile(readable,expanded)
    receipt={'scope':__doc__,'ordinary_lean_compilation_passed':True,
        'finite_partition_kernel_checked':False,'higher_kappa_proven':False,
        'website_statement_comparison_passed':False,'independent_nanoda_passed':False,
        'upload_ready':False,'submitted':False,
        'conditional_statement_namespace':'StructuralW10Cert20261016.FinalConditional',
        'explicit_analytic_hypothesis':'SeparatedFloor',
        'source':str(output.relative_to(ROOT)).replace('\\','/'),
        'source_bytes':output.stat().st_size,'source_sha256':sha(output),
        'readable_source':str(expanded.relative_to(ROOT)).replace('\\','/'),
        'readable_source_sha256':sha(expanded),'compile_receipt_sha256':sha(verified),
        'independent_source_decode_receipt_sha256':sha(decoded)}
    (DEST/'conditional-base-verification.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8')
    print(json.dumps(receipt))

if __name__=='__main__':main()
