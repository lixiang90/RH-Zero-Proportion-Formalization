"""Refresh the honest W10 checkpoint from immutable passed receipts."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    if not __debug__:raise RuntimeError('Checkpoint assertions must remain enabled')
    p=json.loads((HERE/'progress.json').read_bytes())
    bound=p['bound_source_and_receipt_sha256']
    for name,digest in bound.items():assert sha(ROOT/name)==digest,('Changed previously verified input',name)
    for receipt in HERE.glob('*.json'):
        if receipt.stat().st_size>150000:continue
        try:r=json.loads(receipt.read_bytes())
        except (ValueError,UnicodeError):continue
        matched=False
        for module in r.get('modules',[]) if isinstance(r,dict) else []:
            if not isinstance(module,dict) or module.get('passed') is not True:continue
            name=module.get('module','').replace('.','/')+'.lean'
            source=ROOT/name;digest=module.get('source_sha256')
            if source.is_file() and digest==sha(source):
                bound[name]=digest;matched=True
        if matched:bound[str(receipt.relative_to(ROOT)).replace('\\','/')]=sha(receipt)
    audit=json.loads((HERE/'independent-audit-complete.json').read_bytes())
    assert audit['passed'] and audit['required_complete'] and audit['required_all_packed']
    assert audit['unresolved_frontier']==0 and all(x['unchanged_after_audit'] for x in audit['inputs']+audit['packed_inputs'])
    size=json.loads((HERE/'submission-size-assessment.json').read_bytes())
    p.update(scope='Conditional formalization and complete independently audited finite data; full Lean instance and submission remain unfinished',
        complete_discovery_partition=True,complete_independent_integer_audit=True,
        complete_global_floor_proven=False,higher_kappa_proven=False,upload_ready=False,
        submitted=False,official_website_acceptance=False,
        finite_data={key:audit[key] for key in ['branches','numeric_leaves','normalized_empty_leaves',
                    'reflection_leaves','unresolved_frontier','minimum_integer_margin']},
        assembled_source_bytes=size['assembled_source_bytes'],website_source_size_passed=False)
    p['completed'] += [item for item in [
        'Complete immutable finite partition with zero frontier',
        'Independent exact full packed arithmetic and geometry audit',
        'Self-contained conditional proof base ordinary Lean compilation',
        'Finite-check conditional transfer to four actual zeta-count statements',
        'Byte-bound split archives and exact reproduction instructions',
    ] if item not in p['completed']]
    p['remaining']=[
        'Full concrete finite-tree Lean kernel proof (generated source is unverified)',
        'A substantially smaller complete proof encoding or a different analytic certificate',
        'At-most-2000000-byte unconditional standalone source',
        'Website fixed-statement comparison and full default-kernel/nanoda replay of that exact upload',
    ]
    p['generated_unverified_sources']={name:sha(ROOT/name) for name in [
        'StructuralW10Cert20261016/Certificate.lean','StructuralW10Cert20261016/Final.lean']}
    p['complete_finite_evidence_receipts']={str(x.relative_to(ROOT)).replace('\\','/'):sha(x) for x in [
        HERE/'independent-audit-complete.json',HERE/'independent-adaptive-complete.json',
        HERE/'emitted-tree.json',HERE/'proof-input-reduction-manifest.json',
        HERE/'compact-conversion-manifest.json',HERE/'final-manifest-verification.json',
        HERE/'evidence-parts/manifest.json',HERE/'submission-size-assessment.json']}
    p['conditional_base_receipt_sha256']=sha(ROOT/'submission/w10-20261016/conditional-base-verification.json')
    dual_path=ROOT/'verification/w10-20261016/conditional/verification.json'
    if dual_path.exists():
        dual=json.loads(dual_path.read_bytes())
        assert dual['passed'] and dual['scope']=='CONDITIONAL_ONLY' and dual['inputs_unchanged']
        assert not dual['higher_kappa_proven'] and not dual['website_statement_verified']
        p['conditional_dual_kernel_receipt_sha256']=sha(dual_path)
        p['conditional_dual_kernel_checks']={k:dual.get(k,False) for k in [
            'modular_default_kernel_passed','modular_independent_nanoda_passed',
            'standalone_modular_statement_comparison_passed','standalone_default_kernel_passed',
            'standalone_independent_nanoda_passed','standalone_self_statement_comparison_passed']}
        p['conditional_dual_kernel_result_kind']=dual['result_kind']
    p['partial_integer_audits']='Historical snapshot receipts are partial; independent-audit-complete.json is the final full packed integer audit, which is still not a Lean proof.'
    (HERE/'progress.json').write_text(json.dumps(p,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'full_integer_audit':True,'full_lean_floor':False,'upload_ready':False,
                      'verified_module_sources':sum(x.endswith('.lean') for x in bound)}))

if __name__=='__main__':main()
