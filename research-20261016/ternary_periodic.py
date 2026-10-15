"""Uncertified ternary / sparse-large-gap periodic counterexample search."""
import argparse,itertools,json,time
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
import periodic_overlap as p

def bracelets(q,k):
    for w in itertools.product(range(k),repeat=q):
        if w != min(w[i:]+w[:i] for i in range(q)):continue
        rev=w[::-1]
        if w>min(rev[i:]+rev[:i] for i in range(q)):continue
        if any(q%d==0 and w==w[:d]*(q//d) for d in range(1,q)):continue
        yield w

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--max-period',type=int,default=8)
    ap.add_argument('--spans',type=int,default=8);ap.add_argument('--pressure',type=float,default=p.B)
    ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    a=ap.parse_args();p.B=a.pressure
    results=[];st=time.time()
    for q in range(1,a.max_period+1):
        model=p.Periodic(q,a.spans);runs=[]
        words=list(bracelets(q,3))
        # Add sparse gap4..12 phases, surrounded by alternating or all-one gaps.
        extra=[]
        for gap in [3.91,4.95,5.95,7.95,11.95,15.95,23.95,31.7]:
            for mode in [0,1]:
                x=np.resize([1.035] if mode==0 else [1.035,1.965],q).astype(float)
                x[0]=gap;extra.append(x)
        seeds=[(list(w),np.array([1.035,1.965,2.915])[list(w)]) for w in words]
        seeds += [(None,x) for x in extra]
        if q==8:
            seeds.append((None,np.array([1.039336,1.968623,1.038382,1.042147,2.914881,1.043262,1.037940,1.975352])))
        for w,x in seeds:
            sol=minimize(model.fg,x,jac=True,bounds=[(.85,40)]*q,method='L-BFGS-B',
                options={'ftol':1e-15,'gtol':1e-10,'maxiter':1000,'maxls':40})
            runs.append({'word':w,'gaps':sol.x.tolist(),'value':float(sol.fun),
                'gradient_max':float(np.max(np.abs(sol.jac)))})
        runs.sort(key=lambda r:r['value'])
        rec={'period':q,'runs':len(runs),'best':runs[0],'top10':runs[:10],
            'conditional_kappa_percent':100*(p.H-p.B)/(1-runs[0]['value'])}
        results.append(rec);print(json.dumps({k:v for k,v in rec.items() if k!='top10'}),flush=True)
        out={'status':'uncertified periodic candidates; these only upper-bound possible global floors',
            'core_sha256':p.hashlib.sha256(p.RAW).hexdigest(),'spans':a.spans,'pressure':p.B,
            'elapsed_seconds':time.time()-st,'results':results}
        a.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')

if __name__=='__main__':main()
