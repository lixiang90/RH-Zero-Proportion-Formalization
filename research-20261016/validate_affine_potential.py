"""Independent randomized discovery checks of a fixed rational potential.

No exhaustive continuous lower bound is established by this program.
"""
import hashlib,itertools,json
from pathlib import Path
import numpy as np
from scipy.optimize import minimize,differential_evolution
import periodic_overlap as p
import partition_coboundary as part

def main():
    path=Path(__file__).with_name('affine_coboundary.json')
    raw=path.read_bytes();old=json.loads(raw)
    oldmu=np.array([1.042254386484171,1.9726622448599151])
    mu=np.array([1.04,1.97]);den=10**12
    theta=np.array(old['potential'])
    for state in range(128):
        word=np.array([(state>>i)&1 for i in range(7)])
        theta[state,0]+=theta[state,1:]@(mu[word]-oldmu[word])
    nums=np.rint(theta*den).astype(np.int64);theta=nums.astype(float)/den
    rng=np.random.default_rng(90020261016)
    results=[]
    for word in itertools.product(range(2),repeat=8):
        code=sum(v<<i for i,v in enumerate(word));src=code&127;dst=code>>1
        centre=mu[np.array(word)]
        lin=np.r_[theta[src,1:],0]-np.r_[0,theta[dst,1:]]
        const=theta[src,0]-theta[dst,0]-lin@centre
        bounds=[(.85,1.5) if w==0 else (1.5,2.5) for w in word]
        def fg(x):
            f,g=part.fg(x);return f+const+lin@x,g+lin
        starts=[centre]+[np.array([rng.uniform(l,u) for l,u in bounds]) for _ in range(12)]
        sols=[minimize(fg,x,jac=True,bounds=bounds,method='L-BFGS-B',
            options={'ftol':1e-15,'gtol':1e-10,'maxiter':1500,'maxls':40}) for x in starts]
        best=min(sols,key=lambda x:x.fun)
        rec={'code':code,'value':float(best.fun),'gaps':best.x.tolist(),
            'active_potential':bool(np.any(theta[[src,dst]]))}
        results.append(rec)
    # Independent population oracle on only the ten numerically weakest boxes.
    for rec in sorted(results,key=lambda r:r['value'])[:10]:
        code=rec['code'];word=[(code>>i)&1 for i in range(8)];src=code&127;dst=code>>1
        centre=mu[np.array(word)]
        lin=np.r_[theta[src,1:],0]-np.r_[0,theta[dst,1:]]
        const=theta[src,0]-theta[dst,0]-lin@centre
        bounds=[(.85,1.5) if w==0 else (1.5,2.5) for w in word]
        def fun(x):return part.fg(x)[0]+const+lin@x
        sol=differential_evolution(fun,bounds,popsize=12,maxiter=220,tol=1e-10,
            polish=True,seed=8000+code,updating='immediate')
        rec['population_oracle_value']=float(sol.fun)
        if sol.fun<rec['value']:
            rec['value']=float(sol.fun);rec['gaps']=sol.x.tolist()
    result={'status':'fixed rational potential, randomized local and population discovery oracles only; not a proof',
        'input_affine_sha256':hashlib.sha256(raw).hexdigest(),'core_sha256':hashlib.sha256(p.RAW).hexdigest(),
        'denominator':den,'centres_numerator':[104,197],'centres_denominator':100,
        'potential_numerators':{str(i):r.tolist() for i,r in enumerate(nums) if np.any(r)},
        'target_floor_numerator':43,'target_floor_denominator':5000,
        'worst':min(results,key=lambda r:r['value']),'all_results':results}
    out=Path(__file__).with_suffix('.json');out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k not in ['potential_numerators','all_results']},indent=2))

if __name__=='__main__':main()
