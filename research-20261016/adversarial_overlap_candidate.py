"""Independent stochastic attacks on the frozen rational overlap candidate.

Passing these tests is NOT a continuous proof. Parameters and discovery inputs
are read without modification, and every discovered value is an upper bound.
"""
import hashlib,json,time
from pathlib import Path
import numpy as np
from scipy.optimize import minimize,differential_evolution
import periodic_overlap as p
import partition_coboundary as part

def main():
    folder=Path(__file__).resolve().parent;cp=folder/'overlap_rational_candidate.json'
    cr=cp.read_bytes();c=json.loads(cr);den=int(c['common_denominator'])
    theta=np.zeros((128,8));delta=np.zeros(2187)
    for s,row in c['binary_affine_numerators'].items():theta[int(s)]=np.array(row,dtype=float)/den
    for s,v in c['ternary_constant_numerators'].items():delta[int(s)]=int(v)/den
    prior=json.loads((folder/'ternary_potential_oracle.json').read_text());edges=prior['edges']
    lookup={e['code']:e for e in edges};mu=np.array([1.04,1.97]);rng=np.random.default_rng(39020261016)
    def setup(word):
        word=np.array(word);code=sum(int(v)*3**i for i,v in enumerate(word));src=code%2187;dst=code//3
        sr=theta[sum(int(v)<<i for i,v in enumerate(word[:7]))] if 2 not in word[:7] else np.zeros(8)
        dr=theta[sum(int(v)<<i for i,v in enumerate(word[1:]))] if 2 not in word[1:] else np.zeros(8)
        lin=np.r_[sr[1:],0]-np.r_[0,dr[1:]];const=sr[0]-dr[0]+delta[src]-delta[dst]
        if 2 not in word[:7]:const-=sr[1:]@mu[word[:7]]
        if 2 not in word[1:]:const+=dr[1:]@mu[word[1:]]
        bounds=[[(.85,1.5),(1.5,2.5),(2.5,40)][v] for v in word]
        def fg(x):
            f,g=part.fg(x);return f+const+lin@x,g+lin
        def batch(x):
            if x.ndim==1:return fg(x)[0]
            d=x.T@part.TM.T
            xp=d[...,None]+p.FREQ;xm=d[...,None]-p.FREQ
            k=((np.sinc(xp)+np.sinc(xm))*p.CS).sum(axis=-1)/(2*p.K0)
            return x.T@(p.BS+lin)+(k*k)@part.AA+const
        return code,fg,batch,bounds
    def local(word,x):
        code,fg,batch,bounds=setup(word)
        sol=minimize(fg,x,jac=True,bounds=bounds,method='L-BFGS-B',
            options={'ftol':1e-15,'gtol':1e-10,'maxiter':1200,'maxls':40})
        return {'code':code,'value':float(sol.fun),'gaps':sol.x.tolist()}
    st=time.time();runs=[];de_runs=[]
    # Large-gap combinations and random displacements within all near-low boxes.
    lows=[]
    for e in edges:
        value=e['value']+delta[e['src']]-delta[e['dst']]
        if value<.0091:lows.append((value,e))
    lows.sort(key=lambda r:r[0])
    for ix,(old,e) in enumerate(lows):
        n=24 if old<.0087 else 5
        word=np.array(e['word']);bounds=setup(word)[3]
        for _ in range(n):
            x=np.array([rng.uniform(l,u) if w<2 else rng.choice([2.915,3.95,4.95,5.95,7.95,11.95,19.95,31.65],
                p=[.35,.2,.13,.1,.08,.06,.05,.03]) for w,(l,u) in zip(word,bounds)])
            runs.append(local(word,x))
        if ix%128==0:print('random boxes',ix,'elapsed',time.time()-st,flush=True)
    # Independent population oracle on all 10 near-low boxes with a large gap.
    tertiary=[e for v,e in lows if 2 in e['word']][:10]
    for e in tertiary:
        code,fg,batch,bounds=setup(e['word'])
        de=differential_evolution(batch,bounds,popsize=18,maxiter=350,tol=1e-11,
            seed=139000+code,updating='deferred',vectorized=True,polish=False)
        best=local(e['word'],de.x);best['population_value']=float(de.fun);de_runs.append(best)
        print('population',code,best['value'],'elapsed',time.time()-st,flush=True)
    # Global sparse-large-gap attacks include states not selected by the old oracle.
    levels=np.array([1.035,1.965,2.915,3.95,5.95,9.95,19.95,31.65])
    probs=[.43,.34,.15,.03,.02,.015,.01,.005]
    for i in range(2500):
        x=rng.choice(levels,8,p=probs)+rng.normal(0,.007,8)
        word=np.where(x<1.5,0,np.where(x<2.5,1,2));runs.append(local(word,x))
    allruns=runs+de_runs;worst=min(allruns,key=lambda r:r['value'])
    out={'status':'adversarial numerical tests only; no continuous lower bound theorem',
        'candidate_sha256':hashlib.sha256(cr).hexdigest(),'random_local_runs':len(runs),
        'near_low_boxes':len(lows),'population_runs':de_runs,'worst':worst,
        'target_c':.008598,'all_observed_values_above_target':worst['value']>.008598,
        'elapsed_seconds':time.time()-st,'weakest30':sorted(allruns,key=lambda r:r['value'])[:30]}
    (folder/'adversarial_overlap_candidate.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['population_runs','weakest30']},indent=2))

if __name__=='__main__':main()
