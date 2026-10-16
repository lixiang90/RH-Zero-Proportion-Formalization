"""Test a finite-range energy reduction for functional Bellman certificates.

Discarding positive long-span terms is mathematically valid. If the shorter
range energy retains the requested floor, its Markov state has dimension
R-1 instead of nine gaps, opening a different global-proof route. All minima
here are floating local values (upper bounds on infima), never certificates.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,time
import numpy as np
from scipy.optimize import minimize
import window_nine_point_search as base
HERE=Path(__file__).parent;ROOT=HERE.parent
PARAM=ROOT/'research-20261016-followup/window_reweight_rational.json'

def main():
    start=time.monotonic();rng=np.random.default_rng(2026101610);p=json.loads(PARAM.read_bytes())
    c=np.array(p['window_coefficient_numerators_1e9'])/1e9
    pairs=[(i,j) for i,j,v in p['a_upper'] if v];a=np.array([v/1e10 for i,j,v in p['a_upper'] if v]);b=np.array(p['b_numerators'])/1e10
    inc=np.array([[i<=r<j for r in range(9)] for i,j in pairs],float)
    gram=json.loads((HERE/'cover-newwindow-gram.json').read_bytes())
    starts=[np.array([float(F(x)) for x in row['anchor']]) for row in gram['results']]
    starts+=list(rng.choice([1.04,1.97,2.915,3.9],(400,9))+rng.normal(0,.025,(400,9)))
    starts+=[np.full(9,v) for v in [123/128,1.04,1.97,2.915,3.9,5,8,12]]
    H=1680240849522559118481/2500000000000000000000;B=float(b.sum())
    site=float(F(34191001116882886388531117129201664,50760020691785094633026544189453125))
    needed=1-(H-B)/(site+1e-5);rows=[]
    for R in [2,3,4,5,6,9]:
        keep=np.array([j-i<=R for i,j in pairs]);ar=a[keep];ir=inc[keep]
        def energy(g):
            x=ir@g;k=base.profile.bases(x,24)@np.r_[1,c];d=base.profile.bases(x,24,True)@np.r_[1,c]
            return float(ar@(k*k)+b@g),ir.T@(2*ar*k*d)+b
        values=[]
        for g in starts:
            result=minimize(energy,np.maximum(123/128,g),jac=True,bounds=[(123/128,32)]*9,
              method='L-BFGS-B',options={'ftol':1e-14,'gtol':1e-10,'maxiter':500,'maxls':40})
            values.append((float(result.fun),result.x))
        values.sort(key=lambda x:x[0]);v,g=values[0]
        row={'range_R':R,'Bellman_state_dimension':R-1,'terms':int(keep.sum()),
          'observed_minimum_upper_hint':v,'minimum_floor_needed_for_goal_hint':needed,
          'observed_conditional_percent_NOT_BOUND':100*(H-B)/(1-v),
          'observed_margin_over_needed_floor':v-needed,'worst_gaps':g.tolist(),'starts':len(starts)}
        rows.append(row);print(json.dumps(row),flush=True)
        out={'scope':__doc__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'parameter_sha256':hashlib.sha256(PARAM.read_bytes()).hexdigest(),'rows':rows,
          'global_floor_proven':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
        Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
if __name__=='__main__':main()
