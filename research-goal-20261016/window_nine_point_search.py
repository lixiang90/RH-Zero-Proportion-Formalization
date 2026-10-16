"""Alternative nine-point ledger on the same genuinely redesigned window.

The main ten-point proof attempt is untouched. This tests whether one fewer
gap dimension can still meet the full requested improvement margin. Sampled
LP scores and local adversaries are numerical upper evidence, never floors.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,itertools,json,time
import numpy as np
from scipy.optimize import minimize
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
profile=module('nine_window_profile',ROOT/'research-20261016-followup/window_profile_search.py')
wc=module('nine_window_ledger',ROOT/'research-20261016/spectral_wcert_reopt.py')
PARAM=ROOT/'research-20261016-followup/window_reweight_rational.json'

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--rounds',type=int,default=18);ap.add_argument('--starts',type=int,default=80)
    ap.add_argument('--output',type=Path,default=HERE/'window-nine-point-search.json');args=ap.parse_args()
    data=json.loads(PARAM.read_bytes());coeff=np.array(data['window_coefficient_numerators_1e9'])/1e9
    n=9;model=wc.model(n);pairs,inc,am,bm,cap=model;rng=np.random.default_rng(2026101609)
    wc.H=float(profile.H(coeff));wc.base.kernel=lambda x:profile.bases(x,len(coeff))@np.r_[1,coeff]
    wc.DP_CACHE.clear()
    samples=np.array(list(itertools.product([1.04,1.97,2.915],repeat=8)),float)
    samples=np.r_[samples,rng.uniform(.9609375,6,(500,8))]
    for path in (ROOT/'research-20261016').glob('*samples-n9.npz'):
        with np.load(path) as old:samples=np.r_[samples,np.maximum(.9609375,old['gaps'])]
    def features(samples):
        return np.concatenate([(profile.bases(chunk@inc.T,len(coeff))@np.r_[1,coeff])**2 for chunk in np.array_split(samples,max(1,len(samples)//1000))])
    feat=features(samples);history=[];start=time.monotonic()
    for iteration in range(args.rounds):
        a,b,cf,B,kappa=wc.solve(samples,feat,n,model)
        order=np.argsort(feat@a+samples@b);starts=list(samples[order[:args.starts]])
        starts+=list(rng.choice([1.04,1.97,2.915,3.9,4.9],(args.starts//2,8))+rng.normal(0,.025,(args.starts//2,8)))
        starts+=[wc.discrete_dp(n,a,b,pairs,alphabet,8) for alphabet in [(1.04,1.97,2.915),(1.02,1.95,2.9),(1.06,2.,2.94)]]
        for pos in np.argsort(b)[:3]:
            for gap in [12,64,1024]:
                g=np.full(8,1.04);g[pos]=gap;starts.append(g)
        upper=np.maximum(20,np.minimum(4096,.03/np.maximum(b,1e-14)))
        def energy(g):
            x=inc@g;k=profile.bases(x,len(coeff))@np.r_[1,coeff]
            kp=profile.bases(x,len(coeff),True)@np.r_[1,coeff]
            return float(a@(k*k)+b@g),inc.T@(2*a*k*kp)+b
        found=[]
        for g in starts:
            fit=minimize(energy,np.clip(g,.9609375,upper),jac=True,method='L-BFGS-B',
              bounds=list(zip(np.full(8,.9609375),upper)),options={'ftol':1e-14,'gtol':1e-9,'maxiter':500,'maxls':40})
            found.append((float(fit.fun),fit.x))
        found.sort(key=lambda x:x[0]);minimum,g=found[0]
        history.append({'iteration':iteration,'sampled_c':cf,'sampled_score_upper_hint':kappa,
          'adversarial_minimum_upper_hint':minimum,'adversarial_score_not_bound':(wc.H-B)/(1-minimum),
          'violation':cf-minimum,'pressure_B':B,'worst_gaps':g.tolist(),'sample_count':len(samples)})
        out={'scope':__doc__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'window_parameter_sha256':hashlib.sha256(PARAM.read_bytes()).hexdigest(),'points':n,
          'fixed_window_coefficient_numerators_1e9':data['window_coefficient_numerators_1e9'],
          'H_float_hint':wc.H,'a':[[i,j,float(v)] for (i,j),v in zip(pairs,a)],'b':b.tolist(),
          'rank_capacities':(cap@np.linalg.lstsq(am,a,rcond=None)[0]).tolist(),'history':history,
          'global_floor_proven':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
        args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
        print(json.dumps(history[-1]),flush=True)
        new=np.array([g for v,g in found]);samples=np.r_[samples,new];feat=np.r_[feat,features(new)]
        if iteration>=6 and max(abs(h['violation']) for h in history[-3:])<2e-9:break
    np.savez_compressed(args.output.with_suffix('.npz'),gaps=samples,features=feat)
if __name__=='__main__':main()
