"""Research-only obstruction to discarding long-range W10 interactions.

Each reported value is a floating feasible upper bound for a TRUNCATED
objective. It is not a certified global minimum, and it is not a new bound
for the zeta function. The exact proposed parameters are never modified.
"""
from pathlib import Path
from fractions import Fraction
import hashlib,itertools,json,time
import numpy as np
from scipy.optimize import minimize

HERE=Path(__file__).parent;ROOT=HERE.parent
PARAM=ROOT/'research-20261016/spectral-w10-refined-rational.json'
DOC=json.loads(PARAM.read_text());D=DOC['denominator']
TERMS=[(i,j,a/D) for i,j,a in DOC['a_upper'] if a]
INC=np.array([[float(i<=r<j) for r in range(9)] for i,j,a in TERMS])
A=np.array([a for i,j,a in TERMS]);B=np.array(DOC['b_numerators'])/D
RANK=np.array([j-i for i,j,a in TERMS])
COEF=np.array([1.,.012310798,-.015041681,.003867664,.006489926,-.000992327,.005580097,-.006846472,.003781297,-.005670353,.003355089,-.000450523,-.000218483])
FREQ=np.r_[np.sqrt(2)/(2*np.pi),np.arange(1,13)]
NORM=np.sinc(FREQ)@COEF

def dsinc(z):
    out=np.empty_like(z);small=np.abs(z)<1e-4;t=z[small]
    out[small]=-np.pi**2*t/3+np.pi**4*t**3/30-np.pi**6*t**5/840
    t=z[~small];out[~small]=(np.pi*t*np.cos(np.pi*t)-np.sin(np.pi*t))/(np.pi*t*t)
    return out

def amplitude(x):
    u=x[:,None]+FREQ;v=x[:,None]-FREQ
    return (np.sinc(u)+np.sinc(v))@COEF/(2*NORM),(dsinc(u)+dsinc(v))@COEF/(2*NORM)

def objective(x,memory):
    k,dk=amplitude(INC@x);weights=A*(RANK<=memory)
    return float(B@x+weights@(k*k)),B+(weights*2*k*dk)@INC

def main():
    start=time.monotonic();rng=np.random.default_rng(2026101609)
    patterns=list(itertools.product([1.04,1.98],repeat=9))
    seeds=[np.array(patterns[k]) for k in np.linspace(0,len(patterns)-1,96,dtype=int)]
    seeds += [np.full(9,1.04),np.full(9,1.98)]
    seeds += [rng.choice([1.04,1.98,2.97],9) for _ in range(32)]
    h=Fraction(6721684105641188747759983512104999330646,10**40)
    record=Fraction(34191001116882886388531117129201664,50760020691785094633026544189453125)
    threshold=1-(h-Fraction(DOC['B_exact']))/record
    rows=[]
    for memory in range(1,10):
        best=None
        for seed in seeds:
            fit=minimize(lambda x:objective(x,memory),seed,jac=True,bounds=[(.85,18)]*9,
                method='L-BFGS-B',options={'maxiter':500,'ftol':2e-15,'gtol':1e-11})
            if best is None or fit.fun<best.fun:best=fit
        x=best.x;full=objective(x,9)[0]
        rows.append({'memory':memory,'floating_truncated_feasible_value':float(best.fun),
            'gaps':x.tolist(),'full_objective_at_same_gaps':full,
            'can_exceed_current_record_even_if_truncated_lower_bound_were_optimal':bool(best.fun>float(threshold)),
            'success':bool(best.success),'gradient_inf_norm':float(max(abs(best.jac)))})
        seeds.append(x)
        print(json.dumps(rows[-1]),flush=True)
    result={'scope':__doc__,'parameter_sha256':hashlib.sha256(PARAM.read_bytes()).hexdigest(),
        'proposed_c_exact':DOC['proposed_floor_exact'],'record_threshold_c_exact':str(threshold),
        'record_threshold_c_float':float(threshold),'seed_count':len(seeds),
        'results':rows,'seconds':time.monotonic()-start,'new_lean_theorem':False}
    (HERE/'analytic_memory_probe.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')

if __name__=='__main__':main()
