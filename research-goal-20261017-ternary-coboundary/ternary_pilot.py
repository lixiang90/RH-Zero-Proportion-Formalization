"""One fixed full-eight-state ternary antisymmetric potential LP.

Exactly the frozen29171 gap samples/current24 profile and ledger. Breaks
3/2,5/2; no sample compression, new adversary, point fit, parameter scan,
profile/ledger change, cover or Lean. One HiGHS call/time_limit30. Raw
OptimizeResult is written durably before summary. The short-pair proof
only reaches221/25000; a larger mean candidate is not an unconditional kappa.
"""
from pathlib import Path
from fractions import Fraction as F
import gzip,hashlib,json,math,os,sys,time
from types import SimpleNamespace
for name in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[name]='1'
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
sys.path.insert(0,str(ROOT/'tmp/goal-20261016/python-sdp'))
import numpy as np
import scipy
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
OUT=HERE/'ternary-pilot.json';START=HERE/'LP-started.json';RAW=HERE/'raw-result.json'
FOUT=HERE/'float-F.bin.gz';WOUT=HERE/'sample-words.bin.gz';POOL_SHA='7ff5940c1b622d1da96a6ffa1840b578c1f81617fbd766760b208cf93d449f8e'
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
def reverse8(code):
    digits=[]
    for _ in range(8):digits.append(code%3);code//=3
    return sum(v*3**i for i,v in enumerate(digits[::-1]))
def main():
    assert all(not p.exists()for p in [OUT,START,RAW,FOUT,WOUT]);began=time.monotonic();SEP=F(123,128)
    paths=[Path(__file__),ROOT/'research-20261016-followup/window_reweight_rational.json',
        ROOT/'research-goal-20261016/cover-newwindow-gram.json',ROOT/'research-20261016-followup/window_reweight_challenge.json',
        ROOT/'research-20261016-followup/window_profile_24_challenge.json',ROOT/'research-20261016-followup/window_profile_24.npz',
        ROOT/'research-20261016/spectral-wcert-reopt-full-ternary-samples-n10.npz',
        ROOT/'research-goal-20261017-multiwindow/multiwindow_fixed_pair_pilot.py',ROOT/'research-goal-20261017-multiwindow/multiwindow-fixed-pair-pilot.json',
        ROOT/'StructuralGoal20261016/WindowPairCertificate.lean']
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
    aa={(i,j):v for i,j,v in params['a_upper']};assert all(v==aa[9-j,9-i]for(i,j),v in aa.items())and params['b_numerators']==params['b_numerators'][::-1]
    inc=np.array([[i<=r<j for r in range(9)]for i,j,a in edges],dtype=float)
    modes=np.arange(1,25);theta=np.sqrt(2)/2;Z=np.sinc(theta/np.pi);energies=[]
    for start in range(0,len(gaps),512):
        g=gaps[start:start+512];x=g@inc.T
        correction=(np.sinc(x[:,:,None]-modes)+np.sinc(x[:,:,None]+modes))/(2*Z)
        kernel=(np.sinc(x-theta/np.pi)+np.sinc(x+theta/np.pi))/(2*Z)+correction@coef
        energies.append((kernel*kernel)@a+g@b)
    energies=np.concatenate(energies);assert energies.shape==(29171,)and np.all(np.isfinite(energies))
    fbytes=energies.astype('<f8',copy=False).tobytes();FOUT.write_bytes(gzip.compress(fbytes,compresslevel=9,mtime=0))
    canonical=[s for s in range(6561)if s<reverse8(s)];assert len(canonical)==3240
    col={s:k for k,s in enumerate(canonical)}
    def atom(s):
        r=reverse8(s)
        return None if r==s else(col[min(s,r)],1 if s<r else -1)
    classes=np.where(gaps<=1.5,0,np.where(gaps<=2.5,1,2));powers=3**np.arange(8)
    heads=classes[:,:8]@powers;tails=classes[:,1:]@powers
    assert len(set(map(int,heads)))==len(set(map(int,tails)))==6561 and len(set(map(tuple,classes)))==19683
    wordbytes=np.column_stack([heads,tails]).astype('<u2').tobytes();WOUT.write_bytes(gzip.compress(wordbytes,compresslevel=9,mtime=0))
    rr=[];cc=[];dd=[];hist={1:0,2:0,3:0}
    for row,(head,tail)in enumerate(zip(heads,tails)):
        terms={}
        for state,sign in [(int(head),-1),(int(tail),1)]:
            item=atom(state)
            if item is not None:k,orientation=item;terms[k]=terms.get(k,0)+sign*orientation
        terms={k:v for k,v in terms.items()if v};hist[1+len(terms)]+=1
        for k,v in terms.items():rr.append(row);cc.append(k);dd.append(v)
        rr.append(row);cc.append(3240);dd.append(1)
    for k in range(3240):
        for offset,sign in enumerate([-1,1]):
            row=29171+2*k+offset;rr.extend([row,row]);cc.extend([k,3240]);dd.extend([2*sign,-1])
    matrix=coo_matrix((dd,(rr,cc)),shape=(35651,3241)).tocsc();assert matrix.nnz==95930 and hist=={1:404,2:3735,3:25032}
    rhs=np.r_[energies,np.zeros(6480)];objective=np.r_[np.zeros(3240),-1.]
    derived={FOUT.name:{'sha256':digest(FOUT),'bytes':FOUT.stat().st_size,'uncompressed_sha256':hashlib.sha256(fbytes).hexdigest(),'uncompressed_bytes':len(fbytes),'dtype':'little-endian float64','shape':[29171]},
        WOUT.name:{'sha256':digest(WOUT),'bytes':WOUT.stat().st_size,'uncompressed_sha256':hashlib.sha256(wordbytes).hexdigest(),'uncompressed_bytes':len(wordbytes),'dtype':'little-endian uint16','shape':[29171,2]}}
    meta={'scope':__doc__,'source_sha256_start':pins,'sample_sources':counts,'sample_count':29171,'fixed_sample_gap_array_sha256':POOL_SHA,
        'profile_modes':24,'positive_edges':41,'profile_and_ledger_unchanged':True,'separation':str(SEP),'breaks':['3/2','5/2'],
        'class_convention':'0 if g<=3/2;1 if3/2<g<=5/2;2 if5/2<g','word_code':'sum(class(g_j)*3^j),j0..7',
        'potential_states':6561,'palindromic_states_forced_zero':81,'canonical_states':canonical,'independent_potential_variables':3240,
        'canonical_convention':'V(s)=v_col if s<reverse8(s),-v_col if s>reverse8(s),0 if equal',
        'variables':3241,'sample_rows':29171,'state_bound_rows':6480,'inequalities':35651,'matrix_nonzeros':95930,'sample_row_nnz_histogram':hist,
        'constraints':'-V(head)+V(tail)+c<=F_s; +/-2*v_col-c<=0;0<=c<=1/64',
        'method':'highs','time_limit_seconds':30,'LP_calls_authorized':1,'scipy_version':scipy.__version__,'derived_fixed_sample_data':derived,
        'zero_potential_sample_minimum_hint':float(energies.min()),'zero_potential_minimum_sample_index':int(energies.argmin()),
        'existing_short_pair_floor':'221/25000','larger_mean_floor_does_not_alone_improve_unconditional_kappa':True}
    def summary(result,elapsed):
        out={**meta,'phase':'completed_one_fixed_sample_ternary_coupled_potential_LP','LP_calls':1,'LP_status':int(result.status),'LP_message':str(result.message),
            'LP_success':bool(result.success),'LP_seconds':elapsed,'LP_iterations':int(result.nit),'new_gap_points':0,'old_NPZ_kernel_features_used':False}
        if result.x is not None:
            x=np.asarray(result.x);v=x[:3240];c=float(x[3240]);D=10**12;vn=[int(round(float(z)*D))for z in v];cn=math.floor(c*D)
            vr=[F(n,D)for n in vn];cr=F(cn,D);maxabs=max(map(abs,vr));violations=[k for k,z in enumerate(vr)if 2*abs(z)>cr]
            full=np.zeros(6561)
            for s in range(6561):
                term=atom(s)
                if term is not None:k,sgn=term;full[s]=sgn*v[k]
            sampledG=energies+full[heads]-full[tails]
            out.update({'raw_variables':x.tolist(),'raw_canonical_potentials':v.tolist(),'sample_floor_hint':c,
                'sample_floor_gain_over_zero_V_hint':c-float(energies.min()),'minimum_sample_G_hint':float(sampledG.min()),
                'maximum_LP_row_violation_hint':float((matrix@x-rhs).max()),'maximum_potential_absolute_value_hint':float(np.abs(v).max()),
                'nonzero_canonical_potential_hints':int(np.count_nonzero(v)),'floor_upper_cap_active_hint':abs(c-1/64)<1e-9,
                'sample_floor_above_existing_short_pair_hint':c>float(F(221,25000)),
                'fixed_rationalization_rule':'D=10^12; canonical V rounded nearest once; c=floor(float_c*D)/D; no repair',
                'rational_common_denominator':D,'rational_potential_numerators':vn,'rational_c_numerator':cn,'rational_c':str(cr),
                'rational_maximum_potential_absolute_value':str(maxabs),'rational_oscillation_upper':str(2*maxabs),
                'rational_all_state_bounds_absV_le_c_half':not violations,'rational_state_bound_violation_count':len(violations),
                'rational_state_bound_violating_columns':violations,'rational_c_in_range':0<=cr<=F(1,64),
                'candidate_actual_scalar_inequalities_checked':False,'finite_sample_floor_is_not_global_floor':True})
        out.update({'source_sha256_end':pins,'all_sources_unchanged':True,'new_G_requires_closed_class_boundary_proofs':True,
            'old_F_KKT_or_Newton_leaves_reused':False,'global_mean_floor_proven':False,'actual_unconditional_kappa_inferred':False,
            'new_Lean_invocations':0,'cell_exclusion_proven':False,'new_zero_proportion_proven':False})
        return out
    # A complete prospective summary with a mock vector tests every output type,
    # not a second mathematical sample or an optimizer call.
    mock=SimpleNamespace(status=np.int64(0),message='serialization preflight',success=np.bool_(True),nit=np.int64(0),x=np.zeros(3241))
    json.dumps(native(summary(mock,0.)),allow_nan=False)
    json.dumps(native({'result':{'x':np.zeros(3241),'status':np.int64(0),'success':np.bool_(True),'fun':np.float64(0),
        'ineqlin':{'residual':np.zeros(35651),'marginals':np.zeros(35651)},'lower':{'residual':np.zeros(3241),'marginals':np.zeros(3241)},
        'upper':{'residual':np.full(3241,np.inf),'marginals':np.zeros(3241)}}}),allow_nan=False)
    durable(START,{**meta,'complete_JSON_schema_preflight_passed':True,'no_retry_authorized':True});tick=time.monotonic()
    result=linprog(objective,A_ub=matrix,b_ub=rhs,bounds=[(None,None)]*3240+[(0,1/64)],method='highs',options={'time_limit':30.})
    elapsed=time.monotonic()-tick
    durable(RAW,{'source_sha256_start':pins,'derived_fixed_sample_data':derived,'LP_calls_this_model':1,'LP_seconds':elapsed,'result':dict(result)})
    out=summary(result,elapsed)
    for p in paths:assert digest(p)==pins[p.relative_to(ROOT).as_posix()]
    out.update({'raw_result_path':RAW.relative_to(ROOT).as_posix(),'raw_result_sha256':digest(RAW),'serialization_preflight_passed':True,'seconds':time.monotonic()-began})
    durable(OUT,out)
    print(json.dumps(native({k:out.get(k)for k in ['phase','LP_calls','LP_status','LP_message','LP_seconds','zero_potential_sample_minimum_hint',
        'sample_floor_hint','sample_floor_gain_over_zero_V_hint','minimum_sample_G_hint','maximum_LP_row_violation_hint',
        'floor_upper_cap_active_hint','rational_all_state_bounds_absV_le_c_half','rational_state_bound_violation_count',
        'sample_floor_above_existing_short_pair_hint','seconds']}),allow_nan=False),flush=True)
if __name__=='__main__':
    assert __debug__
    main()
