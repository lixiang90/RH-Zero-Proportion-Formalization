"""Close existing failed F: hashes and returned-primal violations only.

No producer import, Sympy, new model assembly, dual extraction or solver call.
Does not repair a point or turn the failed return into a certificate.
"""
from pathlib import Path
from hashlib import sha256
from fractions import Fraction as F
import json
import os
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
RUNTIME=Path('C:/Users/ip/AppData/Roaming/Python/Python314/site-packages/sympy/solvers/simplex.py')
def pin(p):return sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def write_new(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())

def main():
    out=HERE/'failure-closure.json';assert not out.exists()
    failure=load(HERE/'failure.json');terminal=load(HERE/'terminal.json');started=load(HERE/'started.json')
    assert failure['stage']=='validate_primary_primal_dual' and failure['simplex_calls_started']==1
    assert terminal['exit_code']==1 and terminal['child_launches']==1 and terminal['limit_stop'] is None
    assert (HERE/'primary-raw-result.json').exists() and not (HERE/'auxiliary-call-started.json').exists()
    assert not (HERE/'result.json').exists() and not (HERE/'certificate.json').exists()
    before=failure['inputs_sha256_start'];after={name:pin(ROOT/name) for name in before};assert before==after
    assert pin(RUNTIME)==started['runtime_simplex_sha256']
    model=load(HERE/'model.json');raw=load(HERE/'primary-raw-result.json')
    x=[F(0)]+list(map(F,raw['primal']));assert len(x)==10
    violations=[]
    for r in model['rows']:
        value=sum(a*b for a,b in zip(r['coefficients'],x));bound=F(r['rhs'])
        if value>bound:
            violations.append({'row_id':r['row_id'],'kind':r['kind'],'lhs':str(value),
                               'rhs':str(bound),'strict_violation':str(value-bound)})
    assert violations
    result={'schema':'fixed-F-failed-run-closure-v1','outcome':'inconclusive_failed_primal_validation',
        'child_pid':terminal['child_pid'],'child_exit_code':terminal['exit_code'],
        'primary_simplex_calls_returned':1,'auxiliary_simplex_calls':0,
        'auxiliary_not_triggered':'Primary returned normally, not InfeasibleLPError.',
        'all155_rows_feasible':False,'returned_primal_violated_rows':violations,
        'returned_primal_violated_row_count':len(violations),
        'model_sha256':pin(HERE/'model.json'),'raw_result_sha256':pin(HERE/'primary-raw-result.json'),
        'failure_sha256':pin(HERE/'failure.json'),'inputs_sha256_start':before,'inputs_sha256_end':after,
        'external_runtime_identity':{'path':str(RUNTIME),'bytes':RUNTIME.stat().st_size,
            'sha256_start':started['runtime_simplex_sha256'],'sha256_end':pin(RUNTIME),
            'source_file_copied_into_package':False},
        'python_executable':sys.executable,'python_version':sys.version,
        'certificate_verifier_invocations':0,
        'certificate_verifier_not_applicable':'Fail-fast rejected primary before result/certificate existed; verify_certificate.py requires both files.',
        'no_dual_salvage_or_sign_changes':True,'no_solver_retry_or_source_changes':True,
        'new_solver_calls_by_this_closure':0,'new_kernel_queries':0,'Lean_runs':0,
        'model_source_identity_independent_review_pending':True,
        'new_joint_floor_proven':False,'new_unconditional_zero_proportion_proven':False,
        'scope':'Reports the existing invalid returned primal and immutable inputs. No mathematical decision about empty/Lower/Below or actual energy.'}
    write_new(out,result)
    print(json.dumps({'path':out.relative_to(ROOT).as_posix(),'sha256':pin(out),
        'outcome':result['outcome'],'violated_rows':violations}))

if __name__=='__main__':main()
