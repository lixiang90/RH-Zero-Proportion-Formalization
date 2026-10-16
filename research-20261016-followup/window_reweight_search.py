"""Re-optimize pair ledger and pressures after redesigning the actual kernel.

Floating sampled LP / continuous adversaries only. No claimed lower bound.
"""
from __future__ import annotations
import argparse, importlib.util, itertools, json, time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog, minimize
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('win',HERE/'window_profile_search.py')
w=importlib.util.module_from_spec(spec);spec.loader.exec_module(w)
spec=importlib.util.spec_from_file_location('wc',w.OLD/'spectral_wcert_reopt.py')
wc=importlib.util.module_from_spec(spec);spec.loader.exec_module(wc)

def main():
    p=argparse.ArgumentParser();p.add_argument('--source',type=Path,default=HERE/'window_profile_24.json')
    p.add_argument('--output',type=Path,default=HERE/'window_reweight_search.json')
    p.add_argument('--rounds',type=int,default=12);p.add_argument('--starts',type=int,default=80);args=p.parse_args()
    doc=json.loads(args.source.read_text());c=np.array(doc['final_window_coefficient_numerators_1e9'])/1e9
    rng=np.random.default_rng(2026101602);started=time.monotonic();n=10
    wc.H=float(w.H(c))
    wc.base.kernel=lambda x:(w.bases(x,len(c))@np.r_[1,c])
    wc.DP_CACHE.clear()
    pairs,inc,am,bm,cap=wc.model(10)
    samples=np.r_[np.load(w.OLD/'spectral-wcert-reopt-full-ternary-samples-n10.npz')['gaps'],
                 np.load(HERE/'window_profile_24.npz')['gaps'],rng.uniform(.9609375,6,(500,9))]
    samples=np.maximum(.9609375,samples)
    _,index=np.unique(np.round(samples,7),axis=0,return_index=True);samples=samples[np.sort(index)]
    def features(gaps):
        return np.concatenate([(w.bases(chunk@inc.T,len(c))@np.r_[1,c])**2 for chunk in np.array_split(gaps,max(1,len(gaps)//1000))])
    feat=features(samples)
    history=[]
    for it in range(args.rounds):
        a,b,cf,B,kap=wc.solve(samples,feat,n,(pairs,inc,am,bm,cap))
        order=np.argsort(feat@a+samples@b)
        starts=list(samples[order[:args.starts]])
        starts+=list(rng.choice([1.04,1.97,2.915,3.9,4.9],(args.starts//2,9))+rng.normal(0,.015,(args.starts//2,9)))
        starts+=list(rng.uniform(.9609375,6,(args.starts//4,9)))
        starts+=[wc.discrete_dp(n,a,b,pairs,alphabet,9) for alphabet in [(1.04,1.97,2.915),(1.02,1.95,2.9),(1.06,2.,2.94)]]
        starts+=[wc.discrete_dp(n,a,b,pairs,(1.04,1.97,2.915),9,{i:2}) for i in range(9)]
        for i in np.argsort(b)[:3]:
            for v in [12,64,1024]:
                g=np.full(9,1.04);g[i]=v;starts.append(g)
        upper=np.maximum(20,np.minimum(4096,.03/np.maximum(b,1e-14)))
        def fun(g):
            x=inc@g;k=w.bases(x,len(c))@np.r_[1,c];kp=w.bases(x,len(c),True)@np.r_[1,c]
            return float(np.dot(a,k*k)+np.dot(b,g)),inc.T@(2*a*k*kp)+b
        found=[]
        for g in starts:
            fit=minimize(fun,np.clip(g,.9609375,upper),jac=True,method='L-BFGS-B',bounds=list(zip(np.full(9,.9609375),upper)),
                options={'gtol':1e-9,'ftol':1e-14,'maxiter':450,'maxls':40})
            found.append((float(fit.fun),fit.x))
        found.sort(key=lambda r:r[0]);v,g=found[0]
        row={'iteration':it,'sample_floor':cf,'sample_percent_upper':100*kap,'B':B,
            'observed_minimum_upper':v,'observed_percent_not_bound':100*(wc.H-B)/(1-v),
            'violation':cf-v,'adversarial_gaps':g.tolist(),'pair_weights':[[i,j,float(aa)] for (i,j),aa in zip(pairs,a)],
            'pressure':b.tolist(),'span_capacities':(cap@np.linalg.lstsq(am,a,rcond=None)[0]).tolist(),'sample_count':len(samples)}
        history.append(row)
        report={'status':'FLOATING_RESEARCH_ONLY_GLOBAL_FLOOR_UNPROVED','fixed_window_source':str(args.source),
            'window_coefficient_numerators_1e9':doc['final_window_coefficient_numerators_1e9'],
            'H_float_not_bound':wc.H,'separation':.9609375,'history':history,'elapsed_seconds':time.monotonic()-started}
        args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf8')
        print(it,row['observed_percent_not_bound'],row['violation'],B,flush=True)
        new=np.array([g for _,g in found]);samples=np.r_[samples,new];feat=np.r_[feat,features(new)]
        if it>6 and max(abs(r['violation']) for r in history[-3:])<1e-9:break

if __name__=='__main__':main()
