"""Exploratory multiway spectral-defect frames; no formal lower bound is claimed."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import time
import numpy as np
from scipy.optimize import linprog, minimize

CS = np.array([12310798,-15041681,3867664,6489926,-992327,5580097,
    -6846472,3781297,-5670353,3355089,-450523,-218483], dtype=float)/1e9
A = np.sqrt(2)/(2*np.pi)
H = 0.6721684105641188747759983512104999330646
CURRENT = 0.673581220659003966368436248070186379

def sinc_derivative(z):
    z=np.asarray(z,dtype=float)
    safe=np.where(np.abs(z)<1e-4,1,z)
    ordinary=(np.pi*safe*np.cos(np.pi*safe)-np.sin(np.pi*safe))/(np.pi*safe**2)
    series=-np.pi**2*z/3+np.pi**4*z**3/30-np.pi**6*z**5/840
    return np.where(np.abs(z)<1e-4,series,ordinary)

def kernel(x, derivative=False):
    x=np.asarray(x,dtype=float)
    fn=sinc_derivative if derivative else np.sinc
    answer=(fn(x-A)+fn(x+A))/2
    for j,c in enumerate(CS,1): answer += c*(fn(x-j)+fn(x+j))/2
    return answer/np.sinc(A)

def defect(gaps, gradient=False):
    n=len(gaps)+1
    x=np.r_[0,np.cumsum(gaps)]
    distances=x[None,:]-x[:,None]
    gram=kernel(distances)
    eigenvalues,u=np.linalg.eigh(gram)
    psi=np.where(eigenvalues<=2,(eigenvalues-1)**2,2*eigenvalues-3)
    value=float(np.sum(psi)/n)
    if not gradient: return value
    prime=np.where(eigenvalues<=2,2*(eigenvalues-1),2)
    spectral_gradient=(u*prime)@u.T
    flows=np.triu(2/n*spectral_gradient*kernel(distances,True),1)
    grad=np.cumsum(np.sum(flows,axis=1)-np.sum(flows,axis=0))[:-1]
    return value,grad

def mirror_matrix(n):
    matrix=np.zeros((n-1,(n//2)))
    for i in range(n-1): matrix[i,min(i,n-2-i)]=1
    return matrix

def solve_pressure(samples,values,n,kappa):
    mirror=mirror_matrix(n)
    # Charnes--Cooper: t=1/(1-c), u=t*b. This optimizes the sampled
    # fractional score exactly as an LP, rather than one Dinkelbach update.
    rows=np.c_[1-np.asarray(values),-np.asarray(samples)@mirror]
    objective=np.r_[-H,np.sum(mirror,axis=0)]
    lp=linprog(objective,A_ub=rows,b_ub=np.ones(len(values)),bounds=[(1,None)]+[(0,None)]*mirror.shape[1],
               method='highs',options={'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9})
    if not lp.success: raise RuntimeError(lp.message)
    t=float(lp.x[0]);c=1-1/t;b=mirror@lp.x[1:]/t;B=float(np.sum(b))
    return c,b,B,(H-B)/(1-c)

DP_CACHE={}
def discrete_dp(n,b,alphabet=(1.04,1.98,2.92),memory=8):
    """Exact minimizer of a truncated binary/ternary pair model; seed only."""
    q=len(alphabet);memory=min(memory,n-1);states=q**(memory-1);half=states//q if memory>1 else 1
    key=(n,alphabet,memory)
    if key not in DP_CACHE:
        words=np.arange(q**memory,dtype=np.int64);tail=words.copy();distances=np.zeros(len(words));costs=[];value=np.zeros(len(words))
        for _ in range(memory):
            distances+=np.asarray(alphabet)[tail%q];tail//=q
            value=value+2/n*kernel(distances)**2;costs.append(value.copy())
        DP_CACHE[key]=np.asarray(costs)
    costs=DP_CACHE[key]
    if memory==1:
        return np.array([alphabet[int(np.argmin(costs[0,:]+b[i]*np.asarray(alphabet)))] for i in range(n-1)])
    dp=np.full(states,np.inf);dp[0]=0;parents=np.zeros((n-1,states),dtype=np.int64)
    base=np.arange(half);old=base[None,:]+half*np.arange(q)[:,None]
    for index in range(n-1):
        new=np.full(states,np.inf);order=min(memory,index+1)-1
        for bit,gap in enumerate(alphabet):
            candidates=dp[old]+costs[order,old*q+bit]
            choice=np.argmin(candidates,axis=0);newstates=base*q+bit
            new[newstates]=candidates[choice,base]+b[index]*gap
            parents[index,newstates]=old[choice,base]
        dp=new
    state=int(np.argmin(dp));g=[]
    for index in range(n-2,-1,-1):
        g.append(alphabet[state%q]);state=int(parents[index,state])
    return np.array(g[::-1])

def initial_samples(n,rng,size):
    result=[np.full(n-1,d) for d in np.linspace(0,3,241)]
    for _ in range(size):
        kind=rng.integers(0,5)
        if kind==0: g=np.clip(rng.normal(rng.uniform(.85,1.2),.15,n-1),0,4)
        elif kind==1: g=rng.choice([0,.2,.8,1.,1.2,2.,4.],n-1)
        elif kind==2: g=rng.uniform(0,2,n-1)
        elif kind==3:
            g=np.full(n-1,rng.uniform(.85,1.15));g[rng.integers(0,n-1)]=rng.uniform(0,4)
        else: g=np.resize(rng.uniform(0,2,rng.integers(2,min(n,6))),n-1)
        result.append(g)
    return result

def optimize(n,size,rounds,starts,seed,output):
    rng=np.random.default_rng(seed+n)
    samples=initial_samples(n,rng,size)
    for prior_file in output.parent.glob('spectral-defect-frames-*.json'):
        try:
            prior=json.loads(prior_file.read_text())
            for prior_result in prior.get('results',[]):
                if prior_result['n']==n:
                    samples += [np.asarray(row['adversarial_gaps']) for row in prior_result['history']]
        except (ValueError,KeyError): pass
    values=[defect(g) for g in samples]
    history=[];kappa=CURRENT;stable=0
    for iteration in range(rounds):
        c,b,B,kappa=solve_pressure(samples,values,n,kappa)
        ranked=np.argsort(np.asarray(values)+np.asarray(samples)@b)[:max(4,starts//2)]
        candidates=[samples[i] for i in ranked]
        candidates += [np.clip(rng.normal(rng.uniform(.8,1.3),.25,n-1),0,4) for _ in range(starts//2)]
        candidates += [rng.choice([1.04,1.98,2.92],n-1,p=[.5,.4,.1])+rng.normal(0,.035,n-1) for _ in range(starts//2)]
        candidates += [discrete_dp(n,b,alphabet) for alphabet in [(1.04,1.98,2.92),(1.02,1.96,2.91),(1.06,2.,2.94)]]
        for position in np.argsort(b)[:min(4,n-1)]:
            for distance in [8.,32.,128.,1024.]:
                g=np.full(n-1,1.05);g[position]=distance;candidates.append(g)
        upper=np.maximum(8.,np.minimum(4096.,.05/np.maximum(b,1e-12)))
        if iteration==0: candidates += [np.full(n-1,d) for d in [.5,.8,.9,1,1.1,1.5,2]]
        findings=[]
        for start in candidates:
            def fun(g):
                value,grad=defect(g,True)
                return value+np.dot(b,g),grad+b
            res=minimize(fun,np.clip(start,0,upper),jac=True,bounds=list(zip(np.zeros(n-1),upper)),method='L-BFGS-B',
                         options={'ftol':1e-13,'gtol':1e-8,'maxiter':300})
            g=res.x;v=defect(g)
            findings.append((float(v+np.dot(b,g)),g,v))
        findings.sort(key=lambda x:x[0])
        worst,g,v=findings[0]
        history.append({'iteration':iteration,'sample_c':c,'B':B,'sample_kappa':kappa,
            'adversarial_c':worst,'violation':c-worst,'adversarial_gaps':g.tolist()})
        output.with_name(output.stem+f'-progress-n{n}.json').write_text(json.dumps({'n':n,'pressure':b.tolist(),
            'history':history,'sample_count':len(samples),'status':'ongoing numerical exploration'},indent=2)+'\n')
        print(n,iteration,'sample',kappa,'violation',c-worst,'B',B,flush=True)
        for _,g,v in findings:
            samples.append(g);values.append(v)
        stable = stable + 1 if c-worst<2e-8 else 0
        if stable>=3 and iteration>5: break
    safe_sample_c=history[-1]['adversarial_c']
    sample_file=output.with_name(output.stem+f'-samples-n{n}.npz')
    np.savez_compressed(sample_file,gaps=np.asarray(samples),defect_per_point=np.asarray(values),pressure=b)
    return {'n':n,'model':'fractional sliding principal-compression defect, unrestricted nonnegative gaps',
        'status':'numerical exploration only; no certified global minimum; large-gap starts through1024 and cap4096',
        'sample_count':len(samples),'pressure':b.tolist(),'B':B,'sample_c':c,
        'adversarial_c':safe_sample_c,'observed_kappa':(H-B)/(1-safe_sample_c),
        'history':history,'sample_data':str(sample_file),'pressure_LP':'Charnes-Cooper exact sampled fractional objective',
        'adversaries':'continuous random, ternary 8-memory DP, sparse gaps through1024, cap4096'}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--points',type=int,nargs='+',default=[5,9,12,16,24])
    parser.add_argument('--size',type=int,default=400)
    parser.add_argument('--rounds',type=int,default=15)
    parser.add_argument('--starts',type=int,default=10)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();started=time.monotonic()
    baseline={'H':H,'current_kappa':CURRENT,'kernel_samples':{str(x):float(kernel(x)) for x in [.5,.8,.85,.9,.95,1,1.05,1.1]},
        'uniform_frames':{str(n):{str(d):defect(np.full(n-1,d)) for d in [.8,.9,1,1.05,1.1]} for n in [3,5,9,16,24,32,64]}}
    report={'baseline':baseline,'results':[]}
    for n in args.points:
        report['results'].append(optimize(n,args.size,args.rounds,args.starts,20261016,args.output))
        report['elapsed_seconds']=time.monotonic()-started
        args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'elapsed_seconds':report['elapsed_seconds'],'results':[{k:r[k] for k in ['n','observed_kappa','B','adversarial_c']} for r in report['results']]},indent=2))

if __name__=='__main__': main()
