"""Reoptimize the ledger subject to a finite interaction range.

Unlike deleting long terms from the frozen ledger, this reoptimizes both
pair allocations and pressure. A successful shorter-range candidate would
permit a functional Bellman certificate with a smaller state dimension.
Sampled LP and local adversary scores are never global lower bounds.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,itertools,json,time
import numpy as np
from scipy.optimize import minimize
import window_nine_point_search as base
wc=base.wc;profile=base.profile;HERE=Path(__file__).parent
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--points',type=int,default=10);ap.add_argument('--range',type=int,default=6)
    ap.add_argument('--rounds',type=int,default=18);ap.add_argument('--starts',type=int,default=120)
    ap.add_argument('--output',type=Path,default=HERE/'window-range-ledger-n10-r6.json');args=ap.parse_args()
    n=args.points;R=args.range;assert 2<=R<n
    frozen=json.loads(base.PARAM.read_bytes());c=np.array(frozen['window_coefficient_numerators_1e9'])/1e9
    wc.H=float(profile.H(c));wc.base.kernel=lambda x:profile.bases(x,24)@np.r_[1,c];wc.DP_CACHE.clear()
    pairs,inc,am,bm,cap=wc.model(n)
    keep=np.any(am[np.array([j-i<=R for i,j in pairs])]>0,axis=0)
    am=am[:,keep];cap=cap[:,keep];model=pairs,inc,am,bm,cap
    rng=np.random.default_rng(2026101600+100*n+R)
    # Exact ternary configurations are an initial adversarial test set.
    samples=np.array(list(itertools.product([1.04,1.97,2.915],repeat=n-1))) if n<=10 else rng.choice([1.04,1.97,2.915],(12000,n-1))
    samples=np.r_[samples,rng.uniform(123/128,6,(400,n-1))]
    def features(gs):return np.concatenate([(profile.bases(t@inc.T,24)@np.r_[1,c])**2 for t in np.array_split(gs,max(1,len(gs)//1000))])
    feat=features(samples);start=time.monotonic();history=[]
    for iteration in range(args.rounds):
        a,b,cf,B,score=wc.solve(samples,feat,n,model)
        assert all(a[k]==0 for k,(i,j) in enumerate(pairs) if j-i>R)
        def energy(g):
            x=inc@g;k=profile.bases(x,24)@np.r_[1,c];d=profile.bases(x,24,True)@np.r_[1,c]
            return float(a@(k*k)+b@g),inc.T@(2*a*k*d)+b
        order=np.argsort(feat@a+samples@b);starts=list(samples[order[:args.starts]])
        starts+=list(rng.choice([1.04,1.97,2.915,3.9],(args.starts//2,n-1))+rng.normal(0,.025,(args.starts//2,n-1)))
        starts+=[wc.discrete_dp(n,a,b,pairs,alphabet,min(R,9)) for alphabet in [(1.04,1.97,2.915),(1.02,1.95,2.9),(1.06,2.,2.94)]]
        for pos in np.argsort(b)[:3]:
            for gap in [16,64,1024]:
                g=np.full(n-1,1.04);g[pos]=gap;starts.append(g)
        upper=np.maximum(20,np.minimum(4096,.03/np.maximum(b,1e-14)))
        found=[]
        for g in starts:
            fit=minimize(energy,np.clip(g,123/128,upper),jac=True,bounds=list(zip(np.full(n-1,123/128),upper)),
              method='L-BFGS-B',options={'ftol':1e-14,'gtol':1e-10,'maxiter':500,'maxls':40})
            found.append((float(fit.fun),fit.x))
        found.sort(key=lambda x:x[0]);v,g=found[0]
        row={'iteration':iteration,'sampled_score_upper_hint':score,'sampled_floor':cf,
          'observed_minimum_upper_hint':v,'observed_score_NOT_BOUND':(wc.H-B)/(1-v),
          'B':B,'violation':cf-v,'worst_gaps':g.tolist(),'samples':len(samples)}
        history.append(row);print(json.dumps(row),flush=True)
        out={'scope':__doc__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'parameter_sha256':hashlib.sha256(base.PARAM.read_bytes()).hexdigest(),'points':n,'range_R':R,
          'Bellman_state_dimension':R-1,'a':[[i,j,float(v)] for (i,j),v in zip(pairs,a)],'b':b.tolist(),
          'H_hint':wc.H,'history':history,'global_floor_proven':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
        args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
        new=np.array([g for v,g in found]);samples=np.r_[samples,new];feat=np.r_[feat,features(new)]
        if iteration>=6 and max(abs(h['violation']) for h in history[-3:])<1e-8:break
    np.savez_compressed(args.output.with_suffix('.npz'),gaps=samples,features=feat)
if __name__=='__main__':main()
