"""One fixed symmetric profile pair and one finite-sample joint-ledger LP.

mu +/- (cos(2*pi*t)+cos(4*pi*t))/100.  Each actual ledger has rank cap2;
absorbing theta=1/2 gives cap1 independently, total weighted mass cap2.
No adversary, profile/epsilon scan, extra LP, cover, or Lean.  Analytic
AdmWindow/PV/budget conditions for both profiles remain explicit duties.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import hashlib,importlib.util,json,os,sys,time,traceback
os.environ['OPENBLAS_NUM_THREADS']='1'
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
sys.path.insert(0,str(ROOT/'tmp/goal-20261016/python-sdp'))
import numpy as np
import scipy
from scipy.optimize import linprog
OUT=HERE/'multiwindow-fixed-pair-pilot.json'
K=F(34191001116882886388531117129201664,50760020691785094633026544189453125)+F(1,100000)
SEP=F(123,128);EPS=F(1,100)
PI_LO=F(314159265358979323846,10**20);PI_HI=F(314159265358979323847,10**20)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def H_interval(coefficients):
    coslo=sum(F((-1)**r,2**r*factorial(2*r)) for r in range(18));coshi=sum(F((-1)**r,2**r*factorial(2*r)) for r in range(17))
    zlo=sum(F((-1)**r,2**r*factorial(2*r+1)) for r in range(18));zhi=sum(F((-1)**r,2**r*factorial(2*r+1)) for r in range(19))
    plo=sum(c*c*(F(1,2)-1/(4*PI_LO**2*j*j)) for j,c in enumerate(coefficients,1))
    phi=sum(c*c*(F(1,2)-1/(4*PI_HI**2*j*j)) for j,c in enumerate(coefficients,1))
    return F(3,2)-coshi/zlo-phi/zlo**2,F(3,2)-coslo/zhi-plo/zhi**2


def main():
    assert not OUT.exists();began=time.monotonic()
    paths=[Path(__file__),ROOT/'research-20261016-followup/window_reweight_rational.json',
        ROOT/'research-goal-20261016/cover-newwindow-gram.json',ROOT/'research-20261016-followup/window_reweight_challenge.json',
        ROOT/'research-20261016-followup/window_profile_24_challenge.json',ROOT/'research-20261016-followup/window_profile_24.npz',
        ROOT/'research-20261016/spectral-wcert-reopt-full-ternary-samples-n10.npz',
        ROOT/'research-20261016-followup/window_exact_parameters.py',HERE/'multiwindow-diagnostic.json',
        ROOT/'StructuralGoal20261016/WindowProfile.lean',ROOT/'StructuralGoal20261016/WindowEnergy.lean',
        ROOT/'StructuralGoal20261016/WindowMatching.lean',ROOT/'StructuralGoal20261016/WindowDiscreteEnergy.lean']
    pins={p.relative_to(ROOT).as_posix():sha(p) for p in paths};params=json.loads(paths[1].read_bytes());D=params['denominator']
    spec=importlib.util.spec_from_file_location('frozen_existing_pair_interval',paths[7]);ex=importlib.util.module_from_spec(spec);spec.loader.exec_module(ex)
    mean=[F(n,10**9) for n in params['window_coefficient_numerators_1e9']];q=[F(int(j<2)) for j in range(24)]
    profiles=[[u+sign*EPS*v for u,v in zip(mean,q)] for sign in [-1,1]]
    assert all(sum(map(abs,profile))==sum(map(abs,mean))<F(2,25) for profile in profiles)
    pair=[];intervals=[]
    for profile in profiles:
        nums=[int(c*10**9) for c in profile];assert all(F(n,10**9)==c for n,c in zip(nums,profile))
        pair.append(ex.small_pair_bound(nums,SEP));intervals.append(H_interval(profile))
    cap=sum(min(F(1),2*F(p['w_lower'])) for p in pair)/4;assert cap<F(1,64)
    averageH=sum(x[0] for x in intervals)/2;averageHupper=sum(x[1] for x in intervals)/2
    out={'scope':__doc__,'phase':'building_fixed_pair_finite_samples','source_sha256_start':pins,'target':str(K),
        'separation':str(SEP),'profile_mean':list(map(str,mean)),'perturbation_q':list(map(str,q)),'epsilon':str(EPS),'theta':['1/2','1/2'],
        'profile_coefficients':[list(map(str,p)) for p in profiles],'profile_l1':list(map(str,[sum(map(abs,p)) for p in profiles])),
        'profile_positive_lower_from_L1':'67/100','each_profile_H_intervals':[[str(v) for v in z] for z in intervals],
        'average_H_lower':str(averageH),'average_H_upper':str(averageHupper),'average_H_lower_hint':float(averageH),
        'each_profile_short_pair_endpoint':pair,'joint_short_pair_floor_lower':str(cap),
        'short_pair_rule':'2*c <= (min(1,2*wminus)+min(1,2*wplus))/2; positivity and monotonicity on [0,SEP] reduce to existing SEP endpoint',
        'each_original_ledger_rank_capacity':'2','each_theta_absorbed_ledger_rank_capacity':'1','total_absorbed_capacity':'2',
        'actual_profile_derivative_PV_and_budget_checks_completed':False,'actual_AdmWindow_formalized':False,
        'solver_calls_authorized':1,'time_limit_seconds':45,'solver':'scipy HiGHS-IPM','scipy_version':scipy.__version__,
        'global_floor_proven':False,'new_zero_proportion_proven':False,'Lean_invocations':0,'new_gap_configurations':0}
    def save():
        final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==pins
        out.update({'source_sha256_end':final,'all_sources_unchanged':True,'seconds_hint':time.monotonic()-began})
        OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    save()
    try:
        rows=[];counts=[]
        doc=json.loads(paths[2].read_bytes());explicit=np.array([[float(F(v)) for v in row['anchor']] for row in doc['results']])
        rows.extend(explicit);counts.append({'source':paths[2].relative_to(ROOT).as_posix(),'legal_rows':len(explicit)})
        for p in paths[3:5]:
            g=np.array(json.loads(p.read_bytes())['best_gaps']);assert np.all(g>=float(SEP));rows.append(g)
            counts.append({'source':p.relative_to(ROOT).as_posix(),'legal_rows':1})
        for p in paths[5:7]:
            g=np.load(p)['gaps'];legal=g[np.all(g>=float(SEP),axis=1)];rows.extend(legal)
            counts.append({'source':p.relative_to(ROOT).as_posix(),'original_rows':len(g),'legal_rows':len(legal)})
        gaps=np.array(rows);assert len(gaps)==29171
        pairs=[(i,j) for i,j,a in params['a_upper']];inc=np.array([[i<=r<j for r in range(9)] for i,j in pairs],float)
        modes=np.arange(1,25);theta=np.sqrt(2)/2;Z=np.sinc(theta/np.pi);coef=np.array(list(map(float,mean)));fm=[];fp=[]
        for chunk in np.array_split(gaps,1+len(gaps)//512):
            x=chunk@inc.T;U=(np.sinc(x[:,:,None]-modes)+np.sinc(x[:,:,None]+modes))/(2*Z)
            k=(np.sinc(x-theta/np.pi)+np.sinc(x+theta/np.pi))/(2*Z)+U@coef
            dq=(U[:,:,0]+U[:,:,1])/100;fm.append((k-dq)**2);fp.append((k+dq)**2)
        wm=np.concatenate(fm);wp=np.concatenate(fp)
        # Variables Aminus[45],Aplus[45],b_average[9],floor c; A=theta*a.
        matrix=np.c_[-wm,-wp,-gaps,np.ones(len(gaps))];bounds=np.zeros(len(gaps))
        capacity=np.zeros((18,100))
        for side in range(2):
            for rank in range(1,10):
                for e,(i,j) in enumerate(pairs):
                    if j-i==rank:capacity[side*9+rank-1,side*45+e]=1
        matrix=np.r_[matrix,capacity];bounds=np.r_[bounds,np.ones(18)]
        objective=np.r_[np.zeros(90),np.ones(9),-float(K)]
        out.update({'sample_sources':counts,'sample_count':len(gaps),'variables':100,'linear_inequalities':len(bounds),
            'fixed_sample_gap_array_sha256':hashlib.sha256(gaps.tobytes()).hexdigest(),
            'profile_data_do_not_prove_actual_admissibility':True,'phase':'single_fixed_pair_joint_ledger_LP_running'});save();tick=time.monotonic()
        result=linprog(objective,A_ub=matrix,b_ub=bounds,bounds=[(0,None)]*99+[(0,float(cap))],
            method='highs-ipm',options={'time_limit':45.})
        out.update({'LP_status':int(result.status),'LP_message':str(result.message),'LP_success':bool(result.success),
            'LP_seconds_hint':time.monotonic()-tick,'solver_calls':1})
        if result.x is not None:
            x=result.x;floor=float(x[-1]);pressure=float(np.sum(x[90:99]));Hhint=(float(averageH)+float(averageHupper))/2
            out.update({'candidate_absorbed_pair_ledgers':[x[:45].tolist(),x[45:90].tolist()],
                'candidate_original_pair_ledgers':[(2*x[:45]).tolist(),(2*x[45:90]).tolist()],
                'candidate_average_pressure':x[90:99].tolist(),'candidate_floor_on_finite_samples_hint':floor,
                'candidate_average_pressure_sum_hint':pressure,'candidate_finite_sample_ratio_percent_upper_hint':100*(Hhint-pressure)/(1-floor),
                'candidate_target_margin_on_finite_samples_hint':Hhint-pressure+float(K)*floor-float(K),
                'maximum_LP_inequality_violation_hint':float(np.max(matrix@x-bounds)),
                'absorbed_rank_masses_hint':(capacity@x).reshape(2,9).tolist()})
        if result.success:
            out['nonzero_finite_sample_dual_rows_hint']=[[int(i),float(v)] for i,v in enumerate(result.ineqlin.marginals) if abs(v)>1e-12]
            out['candidate_strictly_exceeds_target_on_samples_hint']=out['candidate_target_margin_on_finite_samples_hint']>1e-8
        out['phase']='completed_single_fixed_pair_joint_ledger_LP';save()
    except BaseException as exc:
        out.update({'phase':'exception_stopped','exception':repr(exc),'traceback':traceback.format_exc()});save();raise
    print(json.dumps({k:out[k] for k in ['phase','LP_status','LP_seconds_hint','sample_count','average_H_lower_hint',
        'candidate_finite_sample_ratio_percent_upper_hint','candidate_target_margin_on_finite_samples_hint',
        'candidate_strictly_exceeds_target_on_samples_hint','seconds_hint'] if k in out}),flush=True)


if __name__=='__main__':main()
