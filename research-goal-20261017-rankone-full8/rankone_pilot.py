"""One bounded rank-one feasibility hint for the frozen full-eight model.

Fixed seed: the latest exact714 first moments. One L-BFGS-B call, y in
[-1,1]^9, at most500 iterations/30 seconds. Minimize all5803 normalized
polynomial row violations squared plus all47 normalized q00 violations.
No extra seed, method, row, anchor, sampling or Taylor change. A float
penalty is never a witness; independent Fraction replay is required.
"""
from pathlib import Path
from fractions import Fraction as F
import gzip, hashlib, json, os, sys, time
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1';os.environ['MKL_NUM_THREADS']='1'
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
sys.path.insert(0,str(ROOT/'tmp/goal-20261016/python-sdp'))
import numpy as np
from scipy.optimize import minimize
from scipy.sparse import csr_matrix
OUT=HERE/'rankone-pilot.json';START=HERE/'optimizer-started.json'

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    assert not OUT.exists()and not START.exists();began=time.monotonic()
    paths=[Path(__file__),HERE/'independent_replay.py',
        ROOT/'research-goal-20261017-quartic/quartic-model.json.gz',
        ROOT/'research-goal-20261017-swap-family-quartic/swap-family-normalized.json.gz',
        ROOT/'research-goal-20261017-swap-family-quartic/swap-family-exact-primal.json',
        ROOT/'research-goal-20261017-swap-family-audit/independent-replay.json']
    pins={p.relative_to(ROOT).as_posix():digest(p)for p in paths}
    assert pins[paths[2].relative_to(ROOT).as_posix()]=='080f60fe1a3392e12a37219be13cbd6d9ae305651acebfe01fa1920a74e11233'
    assert pins[paths[3].relative_to(ROOT).as_posix()]=='293ef092f90b1a18e96cf45552afb55a76ebc7b94324126ef04ea567504c248a'
    assert pins[paths[4].relative_to(ROOT).as_posix()]=='f0498ca408bd6b594aeab44cc4594cb698aa6ae8c8ca53c5347b1d6c35090095'
    model=json.loads(gzip.decompress(paths[2].read_bytes()));family=json.loads(gzip.decompress(paths[3].read_bytes()));proof=json.loads(paths[4].read_bytes())
    gate=json.loads(paths[5].read_bytes());assert gate['passed']and gate['new_unsoftened_rows']==8
    assert model['monomials']==family['monomials']and len(model['linear_rows'])==5795 and len(family['additional_linear_rows'])==8
    assert model['slack_index']==family['slack_index']==714 and len(model['PSD_blocks'])==47
    mon=model['monomials'];powers=np.zeros((715,9),dtype=int)
    for k,m in enumerate(mon):
        for j in m:powers[k,j]+=1
    seed_rational=proof['rational_714_moments'][:9];seed=np.array([float(F(v))for v in seed_rational]);assert np.all(np.abs(seed)<=1)
    rows=model['linear_rows']+family['additional_linear_rows'];entries=[];ri=[];ci=[];bound=[];scales=[]
    for r,row in enumerate(rows):
        den=F(row['scale']);assert den>0;bound.append(float(F(row['bound'])/den));scales.append(str(den))
        for k,c in row['coefficients']:
            if k==714:continue
            assert 0<=k<714;ri.append(r);ci.append(k+1);entries.append(float(F(c)/den))
    q_scales=[]
    for b,block in enumerate(model['PSD_blocks']):
        q={k:F(v)for k,v in block['multiplier_polynomial']};den=max([F(1,1000)]+[abs(v)for v in q.values()]);q_scales.append(str(den));bound.append(0.0)
        for k,c in q.items():ri.append(5803+b);ci.append(k);entries.append(-float(c/den))
    a=csr_matrix((entries,(ri,ci)),shape=(5850,715));b=np.array(bound)
    derivative_exponents=[]
    for j in range(9):
        pj=powers.copy();pj[:,j]=np.maximum(pj[:,j]-1,0);derivative_exponents.append(pj)
    evaluation_count=0;iterations=0;last=seed.copy();last_penalty=None;started=time.monotonic();deadline=started+30
    class TimeCap(Exception):pass
    def objective(y):
        nonlocal evaluation_count,last,last_penalty
        if time.monotonic()>=deadline:raise TimeCap()
        values=np.prod(np.power(y[None,:],powers),axis=1)
        derivative=np.column_stack([powers[:,j]*np.prod(np.power(y[None,:],derivative_exponents[j]),axis=1)for j in range(9)])
        violation=np.maximum(a@values-b,0.0);value=float(violation@violation)
        gradient=2*(a@derivative).T@violation
        last=y.copy();last_penalty=value;evaluation_count+=1
        return value,gradient
    def callback(y):
        nonlocal iterations,last
        iterations+=1;last=y.copy()
        if time.monotonic()>=deadline:raise TimeCap()
    START.write_text(json.dumps({'method':'L-BFGS-B','optimizer_calls_authorized':1,'fixed_seed_rational':seed_rational,
        'bounds':[[-1,1]]*9,'maximum_iterations':500,'time_cap_seconds':30,'linear_rows':5803,'q00_rows':47,
        'source_sha256_start':pins},indent=2)+'\n',encoding='utf8')
    result=None;capped=False
    try:result=minimize(objective,seed,method='L-BFGS-B',jac=True,bounds=[(-1.0,1.0)]*9,callback=callback,
        options={'maxiter':500,'maxfun':15000,'ftol':1e-15,'gtol':1e-10,'maxls':20})
    except TimeCap:capped=True
    solve_seconds=time.monotonic()-started
    if result is not None:last=np.array(result.x,dtype=float)
    assert len(last)==9 and np.all(np.isfinite(last))and np.all(last>=-1)and np.all(last<=1)
    values=np.prod(np.power(last[None,:],powers),axis=1);residual=a@values-b
    for p in paths:assert digest(p)==pins[p.relative_to(ROOT).as_posix()]
    out={'scope':__doc__,'status':'single_fixed_seed_rankone_float_candidate_saved_for_exact_replay',
        'source_sha256_start':pins,'source_sha256_end':pins,'all_sources_unchanged':True,'path':model['path'],
        'method':'L-BFGS-B','optimizer_calls':1,'new_seeds':0,'maximum_iterations':500,'time_cap_seconds':30,
        'fixed_seed_rational':seed_rational,'fixed_seed_float':seed.tolist(),'raw_candidate_float':last.tolist(),
        'candidate_rationalized_without_repair':[str(F(str(float(v))))for v in last],
        'conversion':'Fraction(str(float(candidate))) once; no repair or precision adjustment','energy_slack':'0',
        'linear_rows_in_penalty':5803,'q00_rows_in_penalty':47,'q00_normalization_scales':q_scales,
        'q00_normalization_rule':'max(1/1000, maximum absolute multiplier polynomial coefficient)',
        'all_linear_row_scales_preserved':True,'analytic_Jacobian':True,'evaluations':evaluation_count,
        'iterations':int(result.nit)if result is not None else iterations,'time_cap_reached':capped,
        'optimizer_success':bool(result.success)if result is not None else False,
        'optimizer_message':str(result.message)if result is not None else 'time cap before next objective/callback',
        'final_penalty_hint':float(np.maximum(residual,0)@np.maximum(residual,0)),
        'maximum_normalized_violation_hint':float(residual.max()),'negative_row_hints':int((residual>0).sum()),
        'optimizer_seconds':solve_seconds,'source_construction_and_total_seconds':time.monotonic()-began,
        'exact_rankone_witness_claim':False,'actual_F_evaluated':False,'actual_KKT_verified':False,'actual_sublevel_verified':False,
        'SCS_calls':0,'new_actual_scalar_positions':0,'Lean_invocations':0,'cell_exclusion_proven':False,'new_zero_proportion_proven':False}
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:out[k]for k in ['method','iterations','evaluations','time_cap_reached','optimizer_seconds','final_penalty_hint','maximum_normalized_violation_hint','negative_row_hints']},allow_nan=False),flush=True)

if __name__=='__main__':
    assert __debug__
    main()
