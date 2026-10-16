"""Research-only finite-period obstructions / evidence for a coboundary route.

All reported minima are floating feasible upper bounds, never global lower
bounds. No spectral or phase constraints are added to the separated domain.
The pressure and rank totals come unchanged from the exact W10 parameters.
"""
from pathlib import Path
from fractions import Fraction
import hashlib,json,time,sys,itertools
import numpy as np
from scipy.optimize import minimize

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'research-20261016-w10-unconditional'))
import analytic_memory_probe as kernel
PAR=ROOT/'research-20261016/spectral-w10-refined-rational.json'
DOC=json.loads(PAR.read_text());D=DOC['denominator']
RANKS=[sum(Fraction(a,D) for i,j,a in DOC['a_upper'] if j-i==r) for r in range(1,10)]
PRESSURE=sum(Fraction(b,D) for b in DOC['b_numerators'])

def setup(m):
    incidence=np.zeros((9*m,m))
    for r in range(1,10):
        for i in range(m):
            for j in range(r):incidence[(r-1)*m+i,(i+j)%m]+=1
    weights=np.repeat(np.array([float(v) for v in RANKS])/m,m)
    def objective(x):
        spans=incidence@x;k,dk=kernel.amplitude(spans)
        return float(float(PRESSURE)*np.mean(x)+weights@(k*k)),\
            np.full(m,float(PRESSURE)/m)+(weights*2*k*dk)@incidence
    return objective

def main():
    start=time.monotonic();rng=np.random.default_rng(202610160115)
    rows=[]
    for m in [1,2,3,4,5,6,7,8,9,10,12,16]:
        objective=setup(m)
        seeds=[np.full(m,x) for x in [.98,1.02,1.97,2.97]]
        if m<=8:seeds.extend(np.array(p,dtype=float) for p in itertools.product([1.0,2.0],repeat=m))
        else:seeds.extend(rng.choice([1.,2.,3.],m,p=[.55,.4,.05]) for _ in range(128))
        best=None;solutions={}
        for x0 in seeds:
            fit=minimize(objective,x0,jac=True,method='L-BFGS-B',bounds=[(.85,8)]*m,
                options={'ftol':2e-15,'gtol':2e-11,'maxiter':500})
            if best is None or fit.fun<best.fun:best=fit
            pattern=tuple(np.rint(fit.x).astype(int))
            if pattern not in solutions or fit.fun<solutions[pattern][0]:solutions[pattern]=(float(fit.fun),fit.x.tolist())
        row={'period':m,'seed_count':len(seeds),'floating_feasible_upper_bound':float(best.fun),
             'gaps':best.x.tolist(),'gradient_inf_norm':float(max(abs(best.jac))),
             'minimum_not_certified':True,'implied_percent_if_it_were_a_proven_floor':
             100*(float(Fraction(6721684105641188747759983512104999330646,10**40))-float(PRESSURE))/(1-float(best.fun)),
             'top_patterns':[{'gaps':g,'value':v} for v,g in sorted(solutions.values())[:8]]}
        rows.append(row);print(json.dumps({k:v for k,v in row.items() if k!='top_patterns'}),flush=True)
    out={'scope':__doc__,'parameter_sha256':hashlib.sha256(PAR.read_bytes()).hexdigest(),
         'rank_totals_exact':list(map(str,RANKS)),'pressure_exact':str(PRESSURE),
         'results':rows,'seconds':time.monotonic()-start,'new_unconditional_zeta_bound_proven':False}
    (Path(__file__).parent/'global_periodic.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
if __name__=='__main__':main()
