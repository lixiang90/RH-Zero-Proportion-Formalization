"""Write conditional research materials; never mark a website upload ready."""
from pathlib import Path
from decimal import Decimal, localcontext, ROUND_DOWN, ROUND_HALF_UP
from fractions import Fraction
import hashlib, json

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
DEST = ROOT/'submission/w10-20261016'
P = 3338842690820594373879991756052499665323
Q = 4956700000000000000000000000000000000000
OLD = Fraction(34191001116882886388531117129201664,
               50760020691785094633026544189453125)


def main():
    if not __debug__:
        raise RuntimeError('Draft assertions must remain enabled')
    DEST.mkdir(parents=True, exist_ok=True)
    size=json.loads((HERE/'submission-size-assessment.json').read_bytes())
    assembled_bytes=size['assembled_source_bytes']
    assert not size['website_source_size_passed'] and assembled_bytes>2000000
    with localcontext() as context:
        context.prec = 90
        percent = Decimal(100*P)/Decimal(Q)
        gain = percent-Decimal(100*OLD.numerator)/Decimal(OLD.denominator)
        truncated = str(percent.quantize(Decimal('0.0000000001'), rounding=ROUND_DOWN))
        rounded = str(percent.quantize(Decimal('0.0000000001'), rounding=ROUND_HALF_UP))
    status = {
        'status': 'CONDITIONAL_RESEARCH_DRAFT_NOT_SUBMITTABLE',
        'upload_ready': False, 'higher_kappa_proven': False,
        'submitted': False, 'official_website_acceptance': False,
        'full_concrete_lean_instance_proven': False,
        'assembled_source_bytes': assembled_bytes,
        'website_source_size_passed': False,
        'numerator': str(P), 'denominator': str(Q),
        'percent': str(percent), 'website_truncated_percent': truncated,
        'rounded_percent': rounded, 'gain_percentage_points': str(gain),
        'author': 'Li Xiang (lixiang90)', 'model': 'GPT-6', 'harness': 'Codex',
        'license': 'Apache-2.0',
        'title': 'Ten-point Gram-defect certificate with rank-distance nine interactions',
        'method_draft': 'Re-optimised ten-point pair weights and pressures, with a rank-distance nine interaction. Exact finite integer tangent-mixture and tree-flow certificates are intended to discharge the local separated floor 433/50000. The final complete Lean check, source-size compliant upload and independent kernel replays remain required.',
        'local_analytic_premise': 'For all g : Fin 9 -> Real with each gap >= 17/20, Fw W g >= 433/50000.',
        'proved_conditional_module': 'StructuralW10Cert20261016/FinalConditional.lean',
        'finite_check_conditional_module': 'StructuralW10Cert20261016/FiniteConditional.lean',
        'required_remaining': [
            'Complete finite-data Lean proof of the actual separated local floor',
            'Single self-contained UTF-8 upload of at most 2000000 bytes',
            'Fixed-statement comparison and permitted transitive axiom check',
            'Default Lean kernel and independent nanoda replay of the exact upload',
        ],
    }
    bound = {}
    for name in ['review-lean-verification.json', 'finite-conditional-verification.json',
                 'compressed-preflight.json', 'independent-audit-raw-complete.json',
                 'independent-audit-complete.json', 'tailfix-final-merge-manifest.json']:
        path = HERE/name
        if path.exists():
            bound['research-20261016-w10-cert/'+name] = hashlib.sha256(path.read_bytes()).hexdigest()
    status['supporting_receipts_sha256'] = bound
    dual_path=ROOT/'verification/w10-20261016/conditional/verification.json'
    dual_note=''
    if dual_path.exists():
        dual=json.loads(dual_path.read_bytes())
        assert dual['passed'] and dual['scope']=='CONDITIONAL_ONLY' and dual['inputs_unchanged']
        assert not dual['higher_kappa_proven'] and not dual['website_statement_verified']
        keys=['modular_default_kernel_passed','modular_independent_nanoda_passed',
              'standalone_modular_statement_comparison_passed','standalone_default_kernel_passed',
              'standalone_independent_nanoda_passed','standalone_self_statement_comparison_passed']
        status['conditional_dual_kernel_verification']={k:dual.get(k,False) for k in keys}
        status['conditional_dual_kernel_verification']['result_kind']=dual['result_kind']
        bound[str(dual_path.relative_to(ROOT)).replace('\\','/')]=hashlib.sha256(dual_path.read_bytes()).hexdigest()
        if all(dual.get(k) for k in keys[:5]):
            dual_note='''
The [conditional replay receipt](../../verification/w10-20261016/conditional/verification.json)
also records successful default Lean kernel and independent nanoda replay of
the modular conditional roots and the sealed single-file conditional roots,
including their statement comparison and permitted transitive axiom checks.
These roots retain their hypotheses; this is not verification of the website's
unconditional statements or of the full concrete finite certificate.
'''
        elif dual.get('modular_default_kernel_passed') and dual.get('modular_independent_nanoda_passed'):
            dual_note='''
The [conditional replay receipt](../../verification/w10-20261016/conditional/verification.json)
records successful default Lean kernel and independent nanoda replay of the
modular conditional roots. The sealed single-file conditional roots also
passed their own default-kernel replay, transitive axiom check and nanoda
replay. Both remain conditional.

The strict standalone-versus-modular comparison **failed** at
`FinalConditional.SeparatedFloor`: the first detected difference is that real
numeral instances refer to different proof constants after single-file
elaboration. The diagnostic and failure
log are preserved with the receipt. No successful strict cross-version or
website-statement comparison is claimed.
'''
            assert dual.get('standalone_default_kernel_passed') and dual.get('standalone_independent_nanoda_passed')
    audit_path=HERE/'independent-audit-raw-complete.json'
    if audit_path.exists():
        audit=json.loads(audit_path.read_bytes())
        assert audit['passed'] and audit['complete_finite_partition'] and audit['unresolved_frontier']==0
        status['independent_raw_integer_audit']={key:audit[key] for key in [
            'branches','numeric_leaves','normalized_empty_leaves','reflection_leaves',
            'unresolved_frontier','minimum_integer_margin']}
    (DEST/'submission-fields.draft.json').write_text(
        json.dumps(status, ensure_ascii=False, indent=2)+'\n', encoding='utf8')
    (DEST/'README.md').write_text(f'''# W10 conditional submission draft

**Not ready for website submission. No higher unconditional bound is claimed.**

The exact candidate is `{P}/{Q}`, or **{percent}%**.
The website truncates this to **{truncated}%**; the rounded value is **{rounded}%**.
It would exceed [attempt-024](https://www.riemannzeta.fun/submissions/attempt-024)
by **{gain} percentage points** if the remaining finite premise is discharged.

The exact admissibility, pressure and conditional simple/distinct zero-count
transfer have passed ordinary Lean checks. The complete finite data still
require their own full Lean proof. A candidate field draft is available in
[submission-fields.draft.json](submission-fields.draft.json); it is not a
submission manifest and must not be uploaded as a verified result.

The [self-contained conditional base](proof/ConditionalBase.lean) has passed
ordinary Lean compilation in a trusted-package-only environment. Its exact
[readable expansion](uncompressed/ExpandedConditionalBase.lean) and
[byte-bound compilation receipt](conditional-base-verification.json) are
included. This file retains the explicit local-floor hypothesis and is not
the website's unconditional `Solution.lean`.
{dual_note}

Read the [mathematical note](MATHEMATICAL-NOTE.zh-CN.md) and
[conditional counting module](../../StructuralW10Cert20261016/FinalConditional.lean).
The precise analytic premise is `FinalConditional.SeparatedFloor`.
[FiniteConditional.lean](../../StructuralW10Cert20261016/FiniteConditional.lean)
reduces it to an explicit executable finite-check premise; it does not assert
the successful evaluation of the full concrete data.

The website requires one UTF-8 Lean file of at most 2,000,000 bytes and the three
unconditional fixed declarations. The current modular research files do not
satisfy this submission boundary. Final materials are generated only by
`prepare_materials.py` after the exact upload passes all required checks.

The complete finite partition has 95,778 branches, 95,615 numerical leaves,
163 empty leaves and one reflection leaf. Its complete independent integer
audit passed with no unresolved frontier. See the
[reproduction commands](../../research-20261016-w10-cert/REPRODUCE-CERTIFICATE.txt)
and the [full audit receipt](../../research-20261016-w10-cert/independent-audit-complete.json).
The currently assembled complete source is {assembled_bytes:,} bytes. It still needs a
full concrete Lean check and a substantially smaller submission encoding.
''', encoding='utf8')
    print(json.dumps({'upload_ready': False, 'draft': str(DEST/'submission-fields.draft.json')}))


if __name__ == '__main__':
    main()
