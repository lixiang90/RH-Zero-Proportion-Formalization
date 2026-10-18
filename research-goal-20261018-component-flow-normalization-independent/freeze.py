"""Freeze a paper-only independent review; hashes/schema only, no mathematics."""
from pathlib import Path
from hashlib import sha256
import json
import os
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
JOINT=ROOT/'research-goal-20261018-component-flow-normalization-static'
def pin(p):return sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def write(p,obj):
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(obj,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def main():
    assert not (HERE/'audit-files.json').exists() and not (HERE/'independent-review.json').exists()
    assert pin(JOINT/'files.json')=='3b322277203c58be7885b73bf2301024f00bf1e48ac33ae6cfe54aa5daec79ad'
    assert pin(JOINT/'NOTE.zh.md')=='1d5c4d98fad774370a38d0a128fce2e3f75ab1c2f0f645c23266f7acaea47ca8'
    joint=load(JOINT/'files.json')
    for field in ('files','read_only_dependencies','dependencies'):
        for row in joint.get(field,[]):
            p=ROOT/row['path'];assert pin(p)==row['sha256']
            if 'bytes' in row:assert p.stat().st_size==row['bytes']
    write(HERE/'independent-review.json',{
        'schema':'independent-component-flow-normalization-paper-review-v1','passed':True,
        'reviewed_joint_manifest_sha256':pin(JOINT/'files.json'),'reviewed_NOTE_sha256':pin(JOINT/'NOTE.zh.md'),
        'all_joint_sections_read':[1,2,3,4,5,6,7,8,9,10],
        'conditional_normalization_and_integer_RHS_correct_on_paper':True,
        'normalized_minor_bound_at_most4_requires_independent_support_and_raw_units':True,
        'fullrank9_forest_components_equal_order_count_plus1':True,
        'forest_cut_flow_sign_and_at_most_two_Order_solve_correct_on_paper':True,
        'zero_deltaS_needs_same_term_same_domain_dominance_or_explicit_cost':True,
        'restored_base_mass_nonnegative_and_full78_checks_required':True,
        'small_denominator_claim_excludes_raw_mu_base_and_cost':True,
        'primal_tie_zero_base_mass_caveat_preserved':True,
        'canonical_packet_does_not_automatically_inherit_old_Lower':True,
        'alternative_small_model_scaling_and_derivative_min_identity_correct_on_paper':True,
        'FS_point_matrix_rank_determinant_solver_kernel_or_Lean_executions':0,
        'new_support_or_optimality_or_global_efficiency_proved':False,
        'new_actual_Lean_or_global_floor_or_unconditional_kappa_proved':False,
        'source_and_total_runtime_acceptance':'unknown',
        'scope':'Static conditional algebra and interfaces only; no new certificate data, numerical experiment, compilation or optimization.'})
    files=[{'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)}
        for p in sorted(HERE.iterdir()) if p.is_file() and p.name!='audit-files.json']
    refs=[JOINT/'files.json',JOINT/'NOTE.zh.md',
        ROOT/'research-goal-20261018-record-source-audit/snapshot/Solution.lean',
        ROOT/'research-goal-20261018-stageM-component-envelope-preparation/envelope_model.py',
        ROOT/'research-goal-20261018-stageM-component-envelope-preparation/files.json',
        ROOT/'research-goal-20261018-stageM-independent/audit-files.json']
    deps=[{'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)} for p in refs]
    write(HERE/'audit-files.json',{'schema':'independent-component-flow-normalization-static-package-v1',
        'files':files,'read_only_dependencies':deps,'paper_review_passed_under_explicit_conditions':True,
        'numerical_or_FS_matrix_kernel_solver_Lean_executions':0,
        'mutable_governance_files_bound':False,'new_global_floor_or_unconditional_kappa_proven':False,
        'scope':'Conditional paper review only. Raw nonnegative masses/cost/full78 and all-domain/source/runtime gates remain required.'})
    print(json.dumps({'manifest_sha256':pin(HERE/'audit-files.json'),'review_sha256':pin(HERE/'independent-review.json'),
        'files':len(files),'bytes':sum(x['bytes'] for x in files),'static_only':True}))
if __name__=='__main__':main()
