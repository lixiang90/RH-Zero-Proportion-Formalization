"""Static note/immutable source byte identities only; no numerical imports."""
from pathlib import Path
from hashlib import sha256
import json
import os
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
DEPS={
 'research-goal-20261018-record-source-audit/snapshot/Solution.lean':'f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf',
 'research-goal-20261018-stageN2-pooled-component-resumption/files.json':'327db7c23c63aeb0ad49236b59303d04fea93a9fcde524caa5998bcd3637369f',
 'research-goal-20261018-stageN2-pooled-component-resumption/first-Below-readout.json':'3ade873c5f40f065876c8c1917aec528593171514d5dfd54a35ef16b24316324'
}
def pin(p):return sha256(p.read_bytes()).hexdigest()
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)}
def write(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def main():
    deps=[]
    for name,h in DEPS.items():
        p=ROOT/name;assert pin(p)==h;deps.append(row(p))
    receipt={'schema':'N2-curvature-residual-independent-paper-interface-v1','static_review_complete':True,
        'source_interval_curvature_values_not_computed':True,'new_FS_points_kernel_matrix_LP_or_Lean_runs':0,
        'positive_curvature_transfer_and_uniform_payment_unproved_for_this_pair':True,
        'critical_guards':['hull(original_anchor,joint_span_interval)','m_nonnegative_or_baseline_only',
            'original_L0_and_quantized_derivative_payment_unchanged','full52_raw_dual_nonnegative_balance_cost',
            'target_minus_dual_cost_not_primal_gap','exact_quadratic_stationarity_or_explicit_residual_payment'],
        'scope':'Paper algebra and source interface only; no new numerical lower bound or actual exclusion.'}
    write(HERE/'review.json',receipt)
    files=[HERE/n for n in ['REVIEW.zh.md','freeze.py','review.json']]
    manifest={'schema':'N2-curvature-static-interface-package-v1','files':[row(p) for p in files],
        'read_only_dependencies':deps,'mathematical_numerical_executions':0,
        'actual_curvature_bounds_or_global_floor_proven':False,'immutable_future_root_gate_required':True}
    write(HERE/'files.json',manifest)
    print(json.dumps({'manifest':row(HERE/'files.json'),'numerical_runs':0}))
if __name__=='__main__':main()
