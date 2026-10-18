"""Create fixed review materials from existing bytes/receipts; no collector."""
from decimal import Decimal, localcontext
from fractions import Fraction
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = ROOT/'research-goal-20261018-tiny-flatten-preparation-v3/draft/Solution.lean'
EVIDENCE = ROOT/'research-goal-20261019-tiny-kernel-evidence'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def row(path):
    data = path.read_bytes()
    return {'path':path.relative_to(ROOT).as_posix(),'bytes':len(data),'sha256':sha(data)}

def get(path):
    return json.loads(path.read_text(encoding='utf-8'))

def write(name,obj):
    with (HERE/name).open('x',encoding='utf-8',newline='\n') as f:
        json.dump(obj,f,ensure_ascii=False,indent=2);f.write('\n')

def main():
    outputs = ['website-fields.draft.json','verification-status.json','evidence-references.json',
               'mathematical-review.json','files.json']
    assert all(not (HERE/name).exists() for name in outputs)
    s = row(SOURCE)
    assert s['sha256'] == '024902a7ef01ccba2a6c71e54682a31712417e5d3c0b4ead5f6f80ad25fd1a81'
    assert s['bytes'] == 1979280
    manifest = EVIDENCE/'files.json'
    assert sha(manifest.read_bytes()) == '3c2df155099cacfaa587e7b661bf78d932d73006594114d8cc5862c34c6853a8'
    # Read/hash only. Do not execute the evidence collector or its programs.
    for r in get(manifest)['files']:
        actual = row(ROOT/r['path'])
        assert actual['sha256'] == r['sha256'] and actual['bytes'] == r['bytes']
    checks = get(EVIDENCE/'checks.json')
    assert checks['source'] == s
    assert all(checks[k] is True for k in [
        'ordinary_Lean_passed','Comparator_exact_statement_dependency_primitive_passed',
        'transitive_axiom_check_passed','Lean_default_kernel_passed',
        'independent_complete_nanoda_passed'])
    assert checks['nanoda_declarations'] == 75371
    assert checks['nanoda_seconds'] == 427.389541876
    assert checks['full_cold3200s_passed'] is False
    assert checks['official_website_acceptance'] is False
    p = 3337839448633819172184136761695440236797
    q = 4955319193827760237900000000000000000000
    record_q = 4955319193847235264050000000000000000000
    c0 = Fraction(893616123055294719,10**20)
    delta = Fraction(389500523,10**20)
    H = Fraction(6721290091768038344368273523390880473594,10**40)
    B = Fraction(456111945004000000,10**20)
    kappa, baseline = Fraction(p,q),Fraction(p,record_q)
    assert (H-B)/(1-c0-delta) == kappa
    assert (H-B)/(1-c0) == baseline
    assert kappa > baseline
    assert 2*(c0+delta) == c0+(c0+2*delta)
    assert 34980 < 64168
    with localcontext() as ctx:
        ctx.prec = 65
        percent = str(Decimal(100*p)/Decimal(q))
        gain = str(Decimal((kappa-baseline).numerator)/Decimal((kappa-baseline).denominator))
        gain_pp = str(Decimal(100)*Decimal((kappa-baseline).numerator)/Decimal((kappa-baseline).denominator))
    final = ROOT/'StructuralS1RTiny20261018/Phase4/Final.lean'
    text = final.read_text(encoding='utf-8')
    assert '_root_.Ncount T (2*T)' in text and '_root_.N0star T (2*T)' in text
    assert '_root_.Ncount 0 T' in text and '_root_.N0star 0 T' in text
    assert str(p) in text and str(q) in text and str(record_q) in text
    loc = ROOT/'StructuralS1RTiny20261018/Phase1/Localization.lean'
    counting = ROOT/'StructuralS1RTiny20261018/Phase2/Counting.lean'
    assert 'theorem pair_floor (g : Fin 9' in loc.read_text(encoding='utf-8')
    assert 'theorem sum_range_pair_lower' in counting.read_text(encoding='utf-8')
    source_ref = {**s,'relative_from_this_directory':'../../'+s['path'],
                  'copied_into_materials':False,'version':'v3 immutable user-uploaded source'}
    write('website-fields.draft.json',{
      'schema':'reviewable-website-form-fields-not-a-submission-request-v1',
      'suggested_result_name':'single-exception-overlap-20261019',
      'public_display_name_suggestion':'Li Xiang','display_name_requires_user_review':True,
      'authenticated_GitHub_login':'Determined by website sign-in; not supplied by these materials',
      'method':'Geometric incompatibility of consecutive exceptional nine-point windows',
      'score':{'numerator':str(p),'denominator':str(q)},
      'summary':'Strengthens the current s1R nine-point Gram-defect certificate by localizing every separated window below a raised threshold to one exceptional cell or its reflection. Consecutive exceptional windows force their common gap into disjoint intervals in all four orientations. Their energy sum therefore has a stronger lower bound. Pairing the windows yields a summed bound with one fixed boundary loss, and the existing separation, matching and actual zero-counting argument gives unconditional dyadic and cumulative bounds for distinct critical-line zeros. The immutable v3 source retains all inherited attributions and licenses. Ordinary Lean, Comparator/default-kernel and a separately completed independent nanoda replay have passed. The single 3200-second cold run timed out at nanoda; website verification is still reported running, not accepted.',
      'coding_harness_optional':'Codex','AI_model_optional':None,
      'proof_file':source_ref,'automatic_upload_performed':False,
      'website_status':'User-reported running; final acceptance unconfirmed'})
    write('verification-status.json',{
      'schema':'tiny-submission-fixed-status-snapshot-v1','source':s,
      'ordinary_Lean':'PASS','Comparator_exact_statements_dependencies_primitives':'PASS',
      'transitive_axiom_check':'PASS','Lean_default_kernel':'PASS',
      'nanoda_separate_diagnostic':{'status':'PASS','declarations':75371,'seconds':427.389541876,
        'threads':4,'export_sha256':checks['diagnostic_source_export_sha256'],
        'permitted_axioms':['propext','Quot.sound','Classical.choice']},
      'single_cold_3200_second_attempt':{'status':'FAIL','failure_stage':'nanoda',
        'total_elapsed_seconds':checks['previous_full_cold_timeout_seconds'],
        'nanoda_remaining_seconds':checks['previous_full_cold_nanoda_remaining_seconds'],
        'separate_diagnostic_does_not_reclassify_failed_attempt':True},
      'website':{'status':'running','status_basis':'User report relayed by root; no network query in this preparation',
        'reported_digest':'23e3dd765aa27de76938e056f13d3e0f08d849d0e7c39c6f78c62e7640c0a10f',
        'digest_is_not_proof_source_sha256':True,'final_result':None,
        'official_acceptance_confirmed':False,'website_accepted_record_claimed':False},
      'future_status_policy':'Save a new receipt; do not overwrite this frozen snapshot',
      'compiler_network_collector_executions_in_this_preparation':0})
    refs = [manifest,EVIDENCE/'checks.json',
      EVIDENCE/'snapshots/cold-v0/failure.json',
      EVIDENCE/'snapshots/cold-v0/logs/comparator-default-kernel.log',
      EVIDENCE/'snapshots/nanoda-diagnostic/terminal.json',
      EVIDENCE/'snapshots/nanoda-diagnostic/nanoda.log',SOURCE,loc,counting,final,
      ROOT/'research-goal-20261018-tiny-overlap-independent/unique-exception.json']
    write('evidence-references.json',{
      'schema':'submission-external-reference-index-v1','source':source_ref,
      'references':[row(path) for path in refs],
      'external_files_referenced_not_copied_or_modified':True,
      'manifest_scope':'files.json locks only stable files in this material directory'})
    write('mathematical-review.json',{
      'schema':'submission-mathematical-explanation-review-v1',
      'method_scope':'Current s1R W9; nine points/eight gaps, paired on ten points/nine gaps',
      'base_floor':str(c0),'boundary_deficit':str(delta),
      'raised_pair_mean_floor':str(c0+delta),'exception_threshold':str(c0+2*delta),
      'H':str(H),'B9':str(B),'ratio':str(kappa),'bound_percent_decimal':percent,
      'baseline':str(baseline),'ratio_gain_exact':str(kappa-baseline),
      'ratio_gain_decimal':gain,'percentage_point_gain_decimal':gain_pp,
      'same_actual_kernel_and_ledger':True,'arbitrary_separated_windows_not_minimizer_only':True,
      'root_outside_guards_and_reflection_are_required':True,
      'single_exception_source_locator':{'B_exception_id':462,'root':11,'cursor':27229},
      'shared_gap_upper_numerator':34980,'shared_gap_lower_numerator':64168,'scale':32768,
      'four_reflection_orientations_covered':True,
      'finite_sum_lower_bound':'sum E_i >= c*n-delta (single boundary loss)',
      'source_interface_and_exact_ratio_checked':True,
      'new_leaf_kernel_or_optimizer_evaluation':False,
      'new_Lean_or_independent_kernel_execution':False,
      'website_acceptance_inferred':False})
    assert row(SOURCE) == s
    files = [HERE/name for name in ['README.zh.md','MATHEMATICS.zh.md','prepare_materials.py',*outputs[:-1]]]
    write('files.json',{
      'schema':'submission-review-materials-stable-local-files-v1',
      'scope':'Reviewable user submission materials only; current website status unconfirmed',
      'files':[{'path':p.relative_to(HERE).as_posix(),'bytes':len(p.read_bytes()),
                'sha256':sha(p.read_bytes())} for p in files],
      'locks_external_files':False,'old_submission_materials_modified':False,
      'compiler_network_collector_executions':0,'website_accepted_record_claimed':False})
    print(json.dumps({'materials_manifest_sha256':sha((HERE/'files.json').read_bytes()),
                      'source_unchanged':True,'website_acceptance_confirmed':False}))

if __name__ == '__main__':
    main()
