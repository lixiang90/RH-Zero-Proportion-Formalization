"""Floating-point research only: periodic consistency of the frozen W9 energy.

No value printed by this script is a certified lower bound. Each optimized
periodic sequence gives an upper bound on any proposed global floor.
"""
import argparse, ast, hashlib, json, math, re, time
from pathlib import Path
import numpy as np
from scipy.optimize import minimize

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'GramDefect20261015/Core.lean'
RAW = SOURCE.read_bytes()
TXT = RAW.decode('utf-8')
BS = np.array(ast.literal_eval(re.search(r'def BS : List ℕ := (\[[^\n]+)', TXT)[1]), dtype=float) / 1e20
TS = ast.literal_eval(re.search(r'def TS : List Term := (\[[^\n]+)', TXT)[1])
AS = np.array([sum(a for i,j,a,k in TS if j-i == s)/1e20 for s in range(1,9)])
B = float(BS.sum())
CS = np.array([1,12310798/1e9,-15041681/1e9,3867664/1e9,6489926/1e9,
    -992327/1e9,5580097/1e9,-6846472/1e9,3781297/1e9,-5670353/1e9,
    3355089/1e9,-450523/1e9,-218483/1e9])
FREQ = np.r_[math.sqrt(2)/(2*math.pi),np.arange(1,13)]
K0 = math.sqrt(2)*math.sin(math.sqrt(2)/2)
OLD_C = 859538525913875481/1e20
H = 6721684105641188747759983512104999330646/1e40

def sinc_d(x):
    x = np.asarray(x)
    out = np.empty_like(x)
    small = np.abs(x) < 1e-4
    z = math.pi*x[small]
    out[small] = math.pi*(-z/3 + z**3/30-z**5/840+z**7/45360)
    z = math.pi*x[~small]
    out[~small] = math.pi*(z*np.cos(z)-np.sin(z))/z**2
    return out

def w_dw(x):
    x = np.asarray(x)
    xp = x[...,None] + FREQ
    xm = x[...,None] - FREQ
    k = ((np.sinc(xp)+np.sinc(xm))*CS).sum(axis=-1)/(2*K0)
    dk = ((sinc_d(xp)+sinc_d(xm))*CS).sum(axis=-1)/(2*K0)
    return k*k, 2*k*dk

class Periodic:
    def __init__(self, q, spans=8):
        self.q, self.spans = q, spans
        self.coeffs = np.r_[AS,np.full(max(0,spans-8),2.)]
        self.M = np.zeros((spans,q,q))
        for s in range(1,spans+1):
            for i in range(q):
                for t in range(s):
                    self.M[s-1,i,(i+t)%q] += 1
    def fg(self, g):
        d = np.einsum('sij,j->si',self.M,g)
        w,dw = w_dw(d)
        f = B*np.mean(g) + np.einsum('s,si->',self.coeffs,w)/self.q
        gr = np.full(self.q,B/self.q) + np.einsum('s,si,sij->j',self.coeffs,dw,self.M)/self.q
        return float(f),gr

def optimize(q, spans, starts, seed=20261016, low=.85, upper=3.5, warm=None):
    rng = np.random.default_rng(seed+q*100+spans)
    model = Periodic(q,spans)
    records=[]
    initial=[np.full(q,v) for v in [1.01,1.03,1.5,1.95,2.02]]
    initial += [np.resize([1.04,1.97],q),np.resize([1.97,1.04],q)]
    initial += [rng.choice([1.03,1.95],q)+rng.normal(0,.015,q) for _ in range(starts//2)]
    initial += [rng.uniform(low,upper,q) for _ in range(starts//2)]
    if warm is not None:
        initial.insert(0,np.resize(warm,q))
    for x in initial:
        sol=minimize(model.fg,x,jac=True,bounds=[(low,upper)]*q,method='L-BFGS-B',
            options={'ftol':1e-15,'gtol':3e-11,'maxiter':1500,'maxls':40})
        records.append(sol)
    best=min(records,key=lambda s:s.fun)
    g=best.x
    raw_fw=[]
    for r in range(q):
        local=np.array([g[(r+k)%q] for k in range(8)])
        pts=np.r_[0,np.cumsum(local)]
        raw_fw.append(float(BS@local+sum(a/1e20*w_dw(pts[j]-pts[i])[0] for i,j,a,k in TS)))
    return {'period':q,'spans':spans,'best_value':float(best.fun),'gaps':g.tolist(),
        'gradient_max':float(np.max(np.abs(best.jac))), 'runs':len(records),
        'converged_runs':sum(bool(s.success) for s in records),
        'same_minimum_runs':sum(abs(float(s.fun)-best.fun)<1e-9 for s in records),
        'local_W9_min':min(raw_fw),'local_W9_max':max(raw_fw),
        'local_W9_average':sum(raw_fw)/q,
        'conditional_kappa_percent':100*(H-B)/(1-float(best.fun)),
        'floor_above_frozen_c':float(best.fun-OLD_C)}

def necklaces(q):
    """Representatives for binary words modulo rotations and reversal."""
    for code in range(1<<q):
        w=tuple((code>>i)&1 for i in range(q))
        if w != min(w[i:]+w[:i] for i in range(q)):
            continue
        rev=w[::-1]
        if w > min(rev[i:]+rev[:i] for i in range(q)):
            continue
        yield w

def binary_search(q,spans):
    model=Periodic(q,spans)
    all_runs=[]
    for word in necklaces(q):
        x=np.where(word,1.97,1.04)
        sol=minimize(model.fg,x,jac=True,bounds=[(.85,3.5)]*q,method='L-BFGS-B',
            options={'ftol':1e-15,'gtol':3e-11,'maxiter':1500,'maxls':40})
        all_runs.append({'word':list(word),'value':float(sol.fun),'gaps':sol.x.tolist(),
            'gradient_max':float(np.max(np.abs(sol.jac))),'success':bool(sol.success)})
    all_runs.sort(key=lambda x:x['value'])
    return {'period':q,'spans':spans,'patterns':len(all_runs),'best':all_runs[0],
        'top10':all_runs[:10],'values':[r['value'] for r in all_runs]}

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--periods',default='1,2,3,4,5,6,7,8,9,10,12,16,20,24')
    p.add_argument('--spans',default='8,12,16,24,40')
    p.add_argument('--starts',type=int,default=40)
    p.add_argument('--binary',action='store_true')
    p.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=p.parse_args()
    result={'status':'uncertified floating-point discovery; periodic candidates are upper bounds on attainable global floors',
        'source_sha256':hashlib.sha256(RAW).hexdigest(),'B':B,'span_masses':AS.tolist(),
        'frozen_c':OLD_C,'frozen_kappa_percent':100*(H-B)/(1-OLD_C),'results':[]}
    st=time.time()
    for span in map(int,args.spans.split(',')):
        for q in map(int,args.periods.split(',')):
            r=binary_search(q,span) if args.binary else optimize(q,span,args.starts)
            result['results'].append(r)
            print(json.dumps(r),flush=True)
            result['elapsed_seconds']=time.time()-st
            args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')

if __name__=='__main__': main()
