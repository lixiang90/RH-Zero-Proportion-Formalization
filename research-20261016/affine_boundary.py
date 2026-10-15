"""Uncertified overflow checks when the affine potential is zero off its box."""
import hashlib,json
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
import periodic_overlap as p
import partition_coboundary as part

def main():
    inp=Path(__file__).with_name('affine_coboundary.json');raw=inp.read_bytes()
    theta=np.array(json.loads(raw)['potential'])
    oldmu=np.array([1.042254386484171,1.9726622448599151]);mu=np.array([1.04,1.97])
    for state in range(128):
        w=np.array([(state>>i)&1 for i in range(7)])
        theta[state,0]+=theta[state,1:]@(mu[w]-oldmu[w])
    theta=np.rint(theta*1e12)/1e12
    rng=np.random.default_rng(72120261016);results=[]
    for state,row in enumerate(theta):
        if not np.any(row):continue
        word=np.array([(state>>i)&1 for i in range(7)])
        for side in [0,7]:
            inner=[(.85,1.5) if w==0 else (1.5,2.5) for w in word]
            bounds=[(2.5,40)]+inner if side==0 else inner+[(2.5,40)]
            lin=-np.r_[0,row[1:]] if side==0 else np.r_[row[1:],0]
            const=(-row[0]+row[1:]@mu[word]) if side==0 else (row[0]-row[1:]@mu[word])
            def fg(x):
                f,g=part.fg(x);return f+const+lin@x,g+lin
            starts=[]
            for gap in [2.50001,3.01,4.01,6.01,10.01,20.01,35.01]:
                x=np.r_[gap,mu[word]] if side==0 else np.r_[mu[word],gap]
                starts.append(x)
            starts += [np.array([rng.uniform(l,u) for l,u in bounds]) for _ in range(24)]
            sols=[minimize(fg,x,jac=True,bounds=bounds,method='L-BFGS-B',
                options={'ftol':1e-15,'gtol':1e-10,'maxiter':1500,'maxls':40}) for x in starts]
            s=min(sols,key=lambda r:r.fun)
            results.append({'type':'nonzero cross-boundary potential','state':state,'side':side,
                'value':float(s.fun),'gaps':s.x.tolist(),'runs':len(starts)})
    for locations in [[i] for i in range(1,7)]+[[0,7]]:
        bounds=[(2.5,40) if i in locations else (.85,40) for i in range(8)]
        starts=[]
        for _ in range(200):
            x=rng.choice([1.035,1.965],8)+rng.normal(0,.005,8)
            for i in locations:x[i]=rng.choice([2.51,3.01,4.01,6.01,10.01,20.01,35.01])
            starts.append(x)
        sols=[minimize(part.fg,x,jac=True,bounds=bounds,method='L-BFGS-B',
            options={'ftol':1e-15,'gtol':1e-10,'maxiter':1500,'maxls':40}) for x in starts]
        s=min(sols,key=lambda r:r.fun)
        results.append({'type':'both prefix and suffix potential zero','locations':locations,
            'value':float(s.fun),'gaps':s.x.tolist(),'runs':len(starts)})
    out={'status':'uncertified finite randomized optimization; all gaps at least .85; not a global proof',
        'input_sha256':hashlib.sha256(raw).hexdigest(),'core_sha256':hashlib.sha256(p.RAW).hexdigest(),
        'potential_zero_if_any_state_gap_outside':[.85,2.5],
        'worst':min(results,key=lambda r:r['value']),'all_results':results}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in out.items() if k!='all_results'},indent=2))

if __name__=='__main__':main()
