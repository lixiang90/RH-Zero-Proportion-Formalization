"""One fixed-sample clipped-separable antisymmetric W10 potential LP.

Fixed current24 rational profile/ledger and exactly the frozen29171 legal
gap vectors. Four fixed clipped features, four absolute auxiliaries and
one floor. One HiGHS call/time_limit30; no adversary, fit, new samples,
profile/ledger changes, parameter sweep, cover or Lean. Sample constraints
and float kernel values do not prove a continuous/global floor.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib, json, math, os, sys, time
from types import SimpleNamespace
for name in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[name]='1'
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
sys.path.insert(0,str(ROOT/'tmp/goal-20261016/python-sdp'))
import numpy as np
import scipy
from scipy.optimize import linprog
OUT=HERE/'recovery-pilot.json';START=HERE/'recovery-LP-started.json';RAW=HERE/'raw-result.json';POOL_SHA='7ff5940c1b622d1da96a6ffa1840b578c1f81617fbd766760b208cf93d449f8e'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def native(v):
    if isinstance(v,np.ndarray):return native(v.tolist())
    if isinstance(v,np.generic):return native(v.item())
    if isinstance(v,dict):return {str(k):native(w)for k,w in v.items()}
    if isinstance(v,(list,tuple)):return [native(w)for w in v]
    if isinstance(v,float)and not math.isfinite(v):return 'NaN'if math.isnan(v)else 'Infinity'if v>0 else '-Infinity'
    if v is None or isinstance(v,(str,int,float,bool)):return v
    raise TypeError('Unsupported output type: '+repr(type(v)))
def durable(path,data):
    payload=json.dumps(native(data),indent=2,allow_nan=False)+'\n';temp=path.with_suffix(path.suffix+'.partial')
    with temp.open('w',encoding='utf8')as handle:handle.write(payload);handle.flush();os.fsync(handle.fileno())
    os.replace(temp,path)

def main():
    assert not OUT.exists()and not START.exists()and not RAW.exists();began=time.monotonic();SEP=F(123,128)
    paths=[Path(__file__),ROOT/'research-20261016-followup/window_reweight_rational.json',
        ROOT/'research-goal-20261016/cover-newwindow-gram.json',ROOT/'research-20261016-followup/window_reweight_challenge.json',
        ROOT/'research-20261016-followup/window_profile_24_challenge.json',ROOT/'research-20261016-followup/window_profile_24.npz',
        ROOT/'research-20261016/spectral-wcert-reopt-full-ternary-samples-n10.npz',
        ROOT/'research-goal-20261017-multiwindow/multiwindow_fixed_pair_pilot.py',ROOT/'research-goal-20261017-multiwindow/multiwindow-fixed-pair-pilot.json']
    paths.extend([HERE/'failure-files.json',HERE/'failure-receipt.json',HERE/'clipped_pilot.py',HERE/'LP-started.json',HERE/'build_recovery.py'])
    assert digest(HERE/'failure-files.json')=='776052bad06ca5240e47d58c31e83d0dbb17cbe567125d5787828c80d6b36278'
    pins={p.relative_to(ROOT).as_posix():digest(p)for p in paths}
    assert digest(paths[1])=='61ad18366b0234d75c4204bc661446c94f1705c29c3e6041bed0147dd6476f11'
    params=json.loads(paths[1].read_bytes());prior=json.loads(paths[8].read_bytes())
    assert prior['sample_count']==29171 and prior['fixed_sample_gap_array_sha256']==POOL_SHA
    for p in paths[1:7]:assert digest(p)==prior['source_sha256_start'][p.relative_to(ROOT).as_posix()]
    rows=[];counts=[];gram=json.loads(paths[2].read_bytes());explicit=np.array([[float(F(v))for v in row['anchor']]for row in gram['results']])
    rows.extend(explicit);counts.append({'source':paths[2].relative_to(ROOT).as_posix(),'legal_rows':len(explicit)})
    for p in paths[3:5]:
        g=np.array(json.loads(p.read_bytes())['best_gaps']);assert np.all(g>=float(SEP));rows.append(g);counts.append({'source':p.relative_to(ROOT).as_posix(),'legal_rows':1})
    for p in paths[5:7]:
        allg=np.load(p,allow_pickle=False)['gaps'];legal=allg[np.all(allg>=float(SEP),axis=1)];rows.extend(legal)
        counts.append({'source':p.relative_to(ROOT).as_posix(),'original_rows':len(allg),'legal_rows':len(legal)})
    gaps=np.array(rows);assert gaps.shape==(29171,9)and hashlib.sha256(gaps.tobytes()).hexdigest()==POOL_SHA
    assert counts==prior['sample_sources']and np.all(gaps>=float(SEP))
    coef=np.array(params['window_coefficient_numerators_1e9'],dtype=float)/1e9;assert len(coef)==24
    den=params['denominator'];edges=[(i,j,a)for i,j,a in params['a_upper']if a];assert len(edges)==41
    a=np.array([a/den for i,j,a in edges]);b=np.array(params['b_numerators'],dtype=float)/den
    inc=np.array([[i<=r<j for r in range(9)]for i,j,a in edges],dtype=float)
    modes=np.arange(1,25);theta=np.sqrt(2)/2;Z=np.sinc(theta/np.pi);energies=[]
    for start in range(0,len(gaps),512):
        g=gaps[start:start+512];x=g@inc.T
        correction=(np.sinc(x[:,:,None]-modes)+np.sinc(x[:,:,None]+modes))/(2*Z)
        kernel=(np.sinc(x-theta/np.pi)+np.sinc(x+theta/np.pi))/(2*Z)+correction@coef
        energies.append((kernel*kernel)@a+g@b)
    energies=np.concatenate(energies);assert np.all(np.isfinite(energies))
    phi=np.clip(gaps-float(SEP),0.,1.)
    features=np.column_stack([phi[:,j]-phi[:,j+1]-phi[:,7-j]+phi[:,8-j]for j in range(4)])
    matrix=np.c_[-features,np.zeros((len(gaps),4)),np.ones(len(gaps))];rhs=energies.copy();extra=[]
    for j in range(4):
        for sign in [-1.,1.]:
            row=np.zeros(9);row[j]=sign;row[4+j]=-1;extra.append(row)
    row=np.zeros(9);row[4:8]=2;row[8]=-1;extra.append(row)
    matrix=np.r_[matrix,np.array(extra)];rhs=np.r_[rhs,np.zeros(9)];objective=np.r_[np.zeros(8),-1.]
    startdoc={'scope':__doc__,'source_sha256_start':pins,'sample_sources':counts,'sample_count':29171,
        'fixed_sample_gap_array_sha256':POOL_SHA,'profile_and_ledger_unchanged':True,'variables':9,'inequalities':29180,
        'potential_state_gaps':8,'phi':'clip(s-123/128,0,1)','features':['p0-p1-p7+p8','p1-p2-p6+p7','p2-p3-p5+p6','p3-2*p4+p5'],
        'constraints':'-Phi*v+c<=F; +/-v_j<=u_j;2*sum(u)<=c;0<=c<=1/64;u>=0',
        'method':'highs','time_limit_seconds':30,'LP_calls_authorized':1,'scipy_version':scipy.__version__,
        'zero_potential_sample_minimum_hint':float(energies.min()),'zero_potential_minimum_sample_index':int(energies.argmin())}
    def summary(result,elapsed):
        out={**startdoc,'phase':'completed_one_fixed_sample_clipped_potential_LP','LP_calls':1,'LP_status':int(result.status),'LP_message':str(result.message),
            'LP_success':bool(result.success),'LP_seconds':elapsed,'LP_iterations':int(result.nit),'new_gap_points':0,
            'old_NPZ_kernel_features_used':False,'current_exact_profile_numerators_used':params['window_coefficient_numerators_1e9']}
        if result.x is not None:
            x=result.x;v=x[:4];c=float(x[8]);D=10**12
            vn=[int(round(float(z)*D))for z in v];cn=math.floor(c*D);vr=[F(n,D)for n in vn];cr=F(cn,D);osc=2*sum(map(abs,vr),F(0))
            rational_float=np.array(list(map(float,vr))+list(map(float,map(abs,vr)))+[float(cr)])
            out.update({'raw_variables':x.tolist(),'raw_v':v.tolist(),'raw_absolute_auxiliaries':x[4:8].tolist(),'sample_floor_hint':c,
                'sample_floor_gain_over_zero_V_hint':c-float(energies.min()),'maximum_LP_row_violation_hint':float((matrix@x-rhs).max()),
                'minimum_sample_G_hint':float((energies+features@v).min()),'floor_upper_cap_active_hint':abs(c-1/64)<1e-9,
                'oscillation_budget_active_hint':abs(2*np.abs(v).sum()-c)<1e-9,
                'fixed_rationalization_rule':'D=10^12; v rounded nearest once; c=floor(float_c*D)/D; u=abs(v); no repair',
                'rational_common_denominator':D,'rational_v_numerators':vn,'rational_c_numerator':cn,'rational_v':list(map(str,vr)),
                'rational_c':str(cr),'rational_oscillation_upper':str(osc),'rational_oscillation_le_c':osc<=cr,
                'rational_c_in_range':0<=cr<=F(1,64),'rational_budget_slack':str(cr-osc),
                'rational_candidate_sample_row_violation_using_float_F_hint':float((matrix@rational_float-rhs).max()),
                'candidate_exact_actual_scalar_inequalities_checked':False,'finite_sample_floor_is_not_global_floor':True})
        return out
    # Full prospective summary and raw-result type/schema preflight, with
    # a dummy vector only for JSON conversion. No mathematical point is queried.
    mock=SimpleNamespace(status=0,message='serialization preflight only',success=np.bool_(True),nit=np.int64(0),x=np.zeros(9))
    check=summary(mock,0.)
    check.update({'source_sha256_end':pins,'all_sources_unchanged':True,'seconds':0.,'potential_range_proof_instantiated_in_Lean':False,
        'new_G_requires_new_KKT_Newton_and_root_budget':True,'old_F_KKT_or_Newton_leaves_reused':False,
        'global_mean_floor_proven':False,'new_Lean_invocations':0,'cell_exclusion_proven':False,'new_zero_proportion_proven':False})
    json.dumps(native(check),allow_nan=False)
    json.dumps(native({'result':{'status':np.int64(0),'success':np.bool_(True),'x':np.zeros(9),'fun':np.float64(0),
        'ineqlin':{'residual':np.zeros(29180),'marginals':np.zeros(29180)},'lower':{'residual':np.zeros(9),'marginals':np.zeros(9)},
        'upper':{'residual':np.full(9,np.inf),'marginals':np.zeros(9)}}}),allow_nan=False)
    startdoc.update({'complete_JSON_schema_preflight_passed':True,'actual_total_LP_calls_authorized_including_original':2,
        'identical_model_recovery_authorized':True,'prior_result_output_failed':True,'no_further_retry_authorized':True})
    durable(START,startdoc);tick=time.monotonic()
    result=linprog(objective,A_ub=matrix,b_ub=rhs,bounds=[(None,None)]*4+[(0,None)]*4+[(0,1/64)],method='highs',options={'time_limit':30.})
    elapsed=time.monotonic()-tick
    durable(RAW,{'source_sha256_start':pins,'actual_total_LP_calls_including_failed_output':2,'this_recovery_LP_calls':1,'LP_seconds':elapsed,'result':dict(result)})
    out=summary(result,elapsed)
    for p in paths:assert digest(p)==pins[p.relative_to(ROOT).as_posix()]
    out.update({'source_sha256_end':pins,'all_sources_unchanged':True,'seconds':time.monotonic()-began,
        'potential_range_proof_instantiated_in_Lean':False,'new_G_requires_new_KKT_Newton_and_root_budget':True,
        'old_F_KKT_or_Newton_leaves_reused':False,'global_mean_floor_proven':False,'new_Lean_invocations':0,'cell_exclusion_proven':False,'new_zero_proportion_proven':False})
    out.update({'actual_total_LP_calls_including_failed_output':2,'this_recovery_LP_calls':1,'raw_result_path':RAW.relative_to(ROOT).as_posix(),'raw_result_sha256':digest(RAW),'serialization_preflight_passed':True})
    durable(OUT,out)
    print(json.dumps({k:out.get(k)for k in ['phase','LP_status','LP_message','LP_calls','LP_seconds','zero_potential_sample_minimum_hint',
        'sample_floor_hint','sample_floor_gain_over_zero_V_hint','raw_v','rational_oscillation_le_c','rational_budget_slack',
        'floor_upper_cap_active_hint','maximum_LP_row_violation_hint','seconds']}),flush=True)
if __name__=='__main__':
    assert __debug__
    main()
