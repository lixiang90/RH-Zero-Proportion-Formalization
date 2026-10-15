"""Uncertified binary gap partition / de Bruijn coboundary experiment.

Numerical box minima are NOT certified, nor do the boxes cover all legal gaps.
This only tests whether word-level consistency retains an observable gain.
"""
import itertools, json, time
from pathlib import Path
import numpy as np
from scipy.optimize import minimize,linprog
import periodic_overlap as p

TM=np.zeros((len(p.TS),8))
AA=np.array([a/1e20 for i,j,a,k in p.TS])
for n,(i,j,a,k) in enumerate(p.TS): TM[n,i:j]=1

def fg(g):
    w,dw=p.w_dw(TM@g)
    return float(p.BS@g+AA@w),p.BS+(AA*dw)@TM

def main():
    st=time.time()
    edges=[]
    for word in itertools.product(range(2),repeat=8):
        bounds=[(.85,1.5) if w==0 else (1.5,2.5) for w in word]
        starts=[np.where(word,1.95,1.035),np.array([(l+u)/2 for l,u in bounds])]
        runs=[minimize(fg,x,jac=True,bounds=bounds,method='L-BFGS-B',
            options={'ftol':1e-15,'gtol':1e-10,'maxiter':1500,'maxls':40}) for x in starts]
        best=min(runs,key=lambda r:r.fun)
        code=sum(v<<i for i,v in enumerate(word))
        edges.append({'code':code,'src':code&127,'dst':code>>1,'word':list(word),
            'cost':float(best.fun),'gaps':best.x.tolist(),'gradient_max':float(np.max(np.abs(best.jac)))})
    # max c: c - psi(src) + psi(dst) <= cost, psi(0)=0 gauge.
    mat=np.zeros((256,129))
    for i,e in enumerate(edges):
        mat[i,0]=1;mat[i,1+e['src']]-=1;mat[i,1+e['dst']]+=1
    obj=np.r_[-1.,np.zeros(128)]
    sol=linprog(obj,A_ub=mat,b_ub=[e['cost'] for e in edges],
        bounds=[(None,None)]*129,method='highs')
    assert sol.success,sol.message
    dual=-sol.ineqlin.marginals
    active=[dict(e,flow=float(dual[i])) for i,e in enumerate(edges) if dual[i]>1e-8]
    c=float(sol.x[0]);c0=min(e['cost'] for e in edges)
    result={'status':'uncertified local minimizations and LP; restricted binary boxes only; no new theorem',
        'source_sha256':p.hashlib.sha256(p.RAW).hexdigest(),'gap_partition':[[.85,1.5],[1.5,2.5]],
        'local_minimum':c0,'minimum_cycle_mean':c,'coboundary_gain':c-c0,
        'conditional_kappa_percent':100*(p.H-p.B)/(1-c),'active_stationary_edges':active,
        'potential':sol.x[1:].tolist(),'all_edges':edges,'elapsed_seconds':time.time()-st}
    out=Path(__file__).with_suffix('.json')
    out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k not in ['potential','all_edges']},indent=2))

if __name__=='__main__':main()
