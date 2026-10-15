"""Heuristic minima of overlapping nine-point objectives; no certified bound."""
from pathlib import Path
import argparse, json, re, time, itertools
import numpy as np
from scipy.optimize import minimize

ROOT=Path(__file__).resolve().parents[1]
TEXT=(ROOT/'GramDefect20261015/Core.lean').read_text(encoding='utf8')
ATEXT=TEXT[TEXT.index('def aW9 :'):TEXT.index('def bW9 :')]
BTEXT=TEXT[TEXT.index('def bW9 :'):TEXT.index('def W9 :')]
A9={(int(i),int(j)):int(a)/10**14 for i,j,a in re.findall(r'\| (\d+), (\d+) => \((\d+) :',ATEXT)}
B9=np.array([int(b)/10**14 for _,b in re.findall(r'\| (\d+) => \((\d+) :',BTEXT)])
COEFF=np.array([1.,.012310798,-.015041681,.003867664,.006489926,-.000992327,.005580097,-.006846472,.003781297,-.005670353,.003355089,-.000450523,-.000218483])
FREQ=np.r_[np.sqrt(2)/(2*np.pi),np.arange(1,13)]
K0=np.sinc(FREQ)@COEFF
H=.6721684105641188747759983512104999330646
OLD_C=.00859538525913875481

def dsinc(x):
    y=np.empty_like(x); small=np.abs(x)<1e-4; z=x[small]
    y[small]=-np.pi**2*z/3+np.pi**4*z**3/30-np.pi**6*z**5/840
    z=x[~small]
    y[~small]=(np.pi*z*np.cos(np.pi*z)-np.sin(np.pi*z))/(np.pi*z*z)
    return y

def kernel(x):
    plus=x[:,None]+FREQ; minus=x[:,None]-FREQ
    k=(np.sinc(plus)+np.sinc(minus))@COEFF/(2*K0)
    dk=(dsinc(plus)+dsinc(minus))@COEFF/(2*K0)
    return k*k,2*k*dk

def problem(q,fill_tail=False):
    n=8+q; a={}; b=np.zeros(n-1)
    for t in range(q):
        b[t:t+8]+=B9/q
        for (i,j),v in A9.items():a[i+t,j+t]=a.get((i+t,j+t),0)+v/q
    if fill_tail:
        for s in range(9,n):
            for i in range(n-s):a[i,i+s]=2/(n-s)
    keys=[k for k,v in a.items() if v>0]; weights=np.array([a[k] for k in keys])
    incidence=np.array([[int(i<=r<j) for r in range(n-1)] for i,j in keys],dtype=float)
    capacities=[sum(v for (i,j),v in a.items() if j-i==s) for s in range(1,n)]
    assert max(capacities)<2+1e-12 and abs(b.sum()-B9.sum())<1e-14
    def fun(g):
        w,dw=kernel(incidence@g)
        return b@g+weights@w, b+incidence.T@(weights*dw)
    return fun,b,capacities

def main():
    p=argparse.ArgumentParser();p.add_argument('--starts',type=int,default=80)
    p.add_argument('--enumerate-binary',action='store_true')
    p.add_argument('--fill-tail',action='store_true')
    p.add_argument('--q',type=int,nargs='+',default=[1,2,3,4,8])
    p.add_argument('--output',default=str(Path(__file__).with_suffix('.json')))
    args=p.parse_args();rng=np.random.default_rng(20261016); records=[];start=time.monotonic()
    for q in args.q:
        fun,b,cap=problem(q,args.fill_tail);dim=len(b);solutions=[]
        seeds=[np.full(dim,z) for z in [1.,1.25,1.5,1.75,2.]]
        if args.enumerate_binary:
            seeds.extend(np.array(z) for z in itertools.product([1.,2.],repeat=dim))
        else:
            seeds.extend(rng.choice([1.,2.],size=dim)+rng.normal(0,.07,dim) for _ in range(args.starts-5))
        for g in seeds:
            fit=minimize(fun,g,jac=True,method='L-BFGS-B',bounds=[(.85,4.)]*dim,
                         options={'ftol':1e-14,'gtol':1e-9,'maxiter':400,'maxls':30})
            solutions.append((float(fit.fun),fit.x.tolist(),bool(fit.success),int(fit.nit)))
        solutions.sort(key=lambda z:z[0]);best=solutions[0]
        eps=1e-6;point=np.array(best[1]);grad=fun(point)[1]
        numerical=np.array([(fun(point+eps*np.eye(dim)[i])[0]-fun(point-eps*np.eye(dim)[i])[0])/(2*eps) for i in range(dim)])
        assert np.max(np.abs(grad-numerical))<1e-7
        rec={'averaged_windows':q,'points':dim+1,'B':float(b.sum()),'span_capacities':cap,
             'best_observed_local_minimum':best[0], 'gaps':best[1],
             'putative_percent_if_globally_certified':100*(H-b.sum())/(1-best[0]),
             'current_proved_floor':OLD_C,'observed_floor_gap':best[0]-OLD_C,
             'gradient_max_error':float(np.max(np.abs(grad-numerical))),
             'distinct_minima_first_20':solutions[:20]}
        records.append(rec)
        print(json.dumps({k:v for k,v in rec.items() if k!='distinct_minima_first_20'}),flush=True)
    result={'scope':'Heuristic upper bounds on local infima; no new lower bound proved',
            'separation_assumed':.85,'maximum_gap_search_bound':4.,'random_starts':args.starts,
            'enumerate_binary':args.enumerate_binary,
            'fill_tail':args.fill_tail,
            'elapsed_seconds':time.monotonic()-start,'records':records}
    Path(args.output).write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')

if __name__=='__main__':main()
