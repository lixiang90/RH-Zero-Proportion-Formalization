"""Numerical exchange search for larger WCert frames. No certified bound."""
from __future__ import annotations
import argparse, importlib.util, itertools, json, re, time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog, minimize

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('spectral_base',HERE/'spectral_defect_frames.py')
base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
H=base.H;CURRENT=base.CURRENT
FREQ=np.r_[base.A,np.arange(1,13)]
COEFF=np.r_[1.,base.CS]
def fast_w(x):
    """One broadcast over the13 Fourier terms; value and derivative."""
    plus=np.asarray(x)[:,None]+FREQ;minus=np.asarray(x)[:,None]-FREQ
    def derivative(z):
        result=np.empty_like(z);small=np.abs(z)<1e-4;t=z[small]
        result[small]=-np.pi**2*t/3+np.pi**4*t**3/30-np.pi**6*t**5/840
        t=z[~small];result[~small]=(np.pi*t*np.cos(np.pi*t)-np.sin(np.pi*t))/(np.pi*t*t)
        return result
    k=(np.sinc(plus)+np.sinc(minus))@COEFF/(2*np.sinc(base.A))
    dk=(derivative(plus)+derivative(minus))@COEFF/(2*np.sinc(base.A))
    return k*k,2*k*dk

def model(n):
    pairs=list(itertools.combinations(range(n),2));p=len(pairs)
    incidence=np.array([[i<=r<j for r in range(n-1)] for i,j in pairs],dtype=float)
    orbits={};groups=[]
    for i,j in pairs:
        key=min((i,j),(n-1-j,n-1-i))
        if key not in orbits:orbits[key]=len(orbits)
        groups.append(orbits[key])
    pair_map=np.eye(len(orbits))[groups]
    pressure_map=base.mirror_matrix(n)
    capacities=np.array([[j-i==r for i,j in pairs] for r in range(1,n)],dtype=float)@pair_map
    return pairs,incidence,pair_map,pressure_map,capacities

def feature(g,incidence):
    return base.kernel(np.asarray(g)@incidence.T)**2

def solve(samples,features,n,data):
    pairs,incidence,am,bm,cap=data
    # t=1/(1-c), u=t*a, v=t*b; maximizing (H-B)/(1-c).
    rows=np.c_[np.ones(len(samples)),-np.asarray(features)@am,-np.asarray(samples)@bm]
    budget=np.c_[-2*np.ones(n-1),cap,np.zeros((n-1,bm.shape[1]))]
    objective=np.r_[-H,np.zeros(am.shape[1]),np.sum(bm,axis=0)]
    lp=linprog(objective,A_ub=np.r_[rows,budget],b_ub=np.r_[np.ones(len(samples)),np.zeros(n-1)],
        bounds=[(1,64/63)]+[(0,None)]*(am.shape[1]+bm.shape[1]),method='highs',
        options={'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9})
    if not lp.success:raise RuntimeError(lp.message)
    t=float(lp.x[0]);a=am@lp.x[1:1+am.shape[1]]/t;b=bm@lp.x[1+am.shape[1]:]/t
    c=1-1/t;B=float(b.sum())
    return a,b,c,B,(H-B)/(1-c)

DP_CACHE={}
def discrete_dp(n,a,b,pairs,alphabet,memory,forced=None):
    q=len(alphabet);memory=min(memory,n-1);states=q**(memory-1);half=states//q
    key=(alphabet,memory)
    if key not in DP_CACHE:
        words=np.arange(q**memory,dtype=np.int64);tail=words.copy();distance=np.zeros(len(words));costs=[]
        for _ in range(memory):
            distance+=np.asarray(alphabet)[tail%q];tail//=q
            costs.append(base.kernel(distance)**2)
        DP_CACHE[key]=np.array(costs)
    costs=DP_CACHE[key];matrix=np.zeros((n,n))
    for value,(i,j) in zip(a,pairs):matrix[i,j]=value
    dp=np.full(states,np.inf);dp[0]=0;parents=np.zeros((n-1,states),dtype=np.int64)
    radix=np.arange(half);old=radix[None,:]+half*np.arange(q)[:,None]
    for index in range(n-1):
        order=min(memory,index+1);j=index+1
        cost=np.sum(np.array([matrix[j-k,j] for k in range(1,order+1)])[:,None]*costs[:order],axis=0)
        new=np.full(states,np.inf)
        for bit,gap in enumerate(alphabet):
            if forced is not None and index in forced and bit!=forced[index]:continue
            trials=dp[old]+cost[old*q+bit]
            choice=np.argmin(trials,axis=0);states_new=radix*q+bit
            new[states_new]=trials[choice,radix]+b[index]*gap
            parents[index,states_new]=old[choice,radix]
        dp=new
    state=int(np.argmin(dp));g=[]
    for index in range(n-2,-1,-1):
        g.append(alphabet[state%q]);state=int(parents[index,state])
    return np.array(g[::-1])

def run(n,args):
    rng=np.random.default_rng(20261016+n);data=model(n);pairs,incidence,am,bm,cap=data
    samples=[np.array(g) for g in itertools.product([1.04,1.98],repeat=n-1)]
    samples += [np.full(n-1,d) for d in np.linspace(.8,4,201)]
    samples += [rng.choice([.8,1.04,1.98,2.92,3.9],n-1)+rng.uniform(0,.04,n-1) for _ in range(args.size)]
    for path in HERE.glob(f'spectral-wcert-reopt*-samples-n{n}.npz'):
        with np.load(path) as prior:samples.extend(prior['gaps'])
    if n==10 and (HERE/'spectral-w10-full-ternary.npz').exists():
        with np.load(HERE/'spectral-w10-full-ternary.npz') as prior:samples.extend(prior['gaps'])
    # Include parent overlap minima, all known spectral minima, and this run's earlier minima.
    for path in HERE.glob('*.json'):
        try:doc=json.loads(path.read_text(encoding='utf8'))
        except (ValueError,OSError):continue
        records=doc.get('records',[])+doc.get('results',[])
        if doc.get('n')==n:records.append(doc)
        for rec in records:
            g=rec.get('gaps')
            if g is not None and len(g)==n-1:samples.append(np.maximum(.8,g))
            for row in rec.get('history',[]):
                g=row.get('adversarial_gaps')
                if g is not None and len(g)==n-1:samples.append(np.maximum(.8,g))
    features=list(feature(samples,incidence));history=[]
    for iteration in range(args.rounds):
        a,b,c,B,kappa=solve(samples,features,n,data)
        ranked=np.argsort(np.asarray(features)@a+np.asarray(samples)@b)[:max(64,args.starts*3)]
        starts=[samples[i] for i in ranked]
        starts += [rng.choice([1.04,1.98,2.92],n-1,p=[.5,.4,.1])+rng.normal(0,.035,n-1) for _ in range(args.starts)]
        starts += [rng.choice([1.04,1.98,2.92,3.9,4.9],n-1)+rng.normal(0,.025,n-1) for _ in range(args.starts//3)]
        starts += [discrete_dp(n,a,b,pairs,alphabet,memory) for alphabet,memory in
            [((1.04,1.98,2.92),min(n-1,11)),((1.02,1.96,2.91),min(n-1,11)),
             ((1.06,2.,2.94),min(n-1,11)),((1.04,1.98,2.92,3.9),9)]]
        starts += [discrete_dp(n,a,b,pairs,(1.04,1.97,2.915),min(n-1,11),{i:2}) for i in range(n-1)]
        for position in np.argsort(b)[:min(4,n-1)]:
            for distance in [8.,32.,128.,4096.]:
                g=np.full(n-1,1.05);g[position]=distance;starts.append(g)
        if iteration%4==0:
            for i,j in itertools.combinations(range(n-1),2):
                g=np.full(n-1,1.04);g[i]=2.92;g[j]=1.98;starts.append(g)
        upper=np.maximum(8.,np.minimum(4096.,.025/np.maximum(b,1e-12)))
        def fun(g):
            value,derivative=fast_w(incidence@g)
            return float(np.dot(a,value)+np.dot(b,g)),incidence.T@(a*derivative)+b
        findings=[]
        for g in starts:
            fit=minimize(fun,np.clip(g,.8,upper),jac=True,bounds=list(zip(np.full(n-1,.8),upper)),
                method='L-BFGS-B',options={'ftol':1e-14,'gtol':1e-9,'maxiter':400,'maxls':30})
            findings.append((float(fit.fun),fit.x.copy()))
        findings.sort(key=lambda row:row[0]);worst,g=findings[0]
        actual=(H-B)/(1-worst)
        row={'iteration':iteration,'sample_kappa':kappa,'sample_c':c,'B':B,'adversarial_c':worst,
            'observed_kappa':actual,'violation':c-worst,'adversarial_gaps':g.tolist()}
        history.append(row)
        record={'n':n,'scope':'Numerical exchange; sampled LP upper bound and adversarial local upper bound, not a proved floor',
            'a':[[i,j,float(value)] for (i,j),value in zip(pairs,a)],'b':b.tolist(),
            'span_capacities':[float(sum(value for (i,j),value in zip(pairs,a) if j-i==d)) for d in range(1,n)],
            'sample_count':len(samples),'history':history,'status':'ongoing'}
        args.output.with_name(args.output.stem+f'-progress-n{n}.json').write_text(json.dumps(record,indent=2)+'\n')
        print(n,iteration,'sample',kappa,'actual',actual,'violation',c-worst,'B',B,flush=True)
        for _,g in findings:
            samples.append(g);features.append(feature(g,incidence))
        if iteration>6 and max(r['violation'] for r in history[-3:])<2e-8:break
    sample_path=args.output.with_name(args.output.stem+f'-samples-n{n}.npz')
    np.savez_compressed(sample_path,gaps=np.asarray(samples),features=np.asarray(features))
    record.update(status='Numerical exploration complete; no certified global minimum',sample_data=str(sample_path))
    return record

def main():
    p=argparse.ArgumentParser();p.add_argument('--points',type=int,nargs='+',default=[10,11,12])
    p.add_argument('--size',type=int,default=400);p.add_argument('--rounds',type=int,default=40)
    p.add_argument('--starts',type=int,default=24);p.add_argument('--output',type=Path,default=HERE/'spectral-wcert-reopt.json')
    args=p.parse_args();started=time.monotonic();report={'H':H,'current_kappa':CURRENT,'results':[]}
    for n in args.points:
        report['results'].append(run(n,args));report['elapsed_seconds']=time.monotonic()-started
        args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'elapsed_seconds':report['elapsed_seconds'],'results':[{**{'n':r['n']},**r['history'][-1]} for r in report['results']]},indent=2))

if __name__=='__main__':main()
