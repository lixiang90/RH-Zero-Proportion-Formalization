"""Explicit admissible longer-rank W_R construction; exploratory local minima.

The rank/pressure identities are checked exactly. Local optimization gives
feasible UPPER bounds only and does not establish any separated floor.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,sys,time
import numpy as np
from scipy.optimize import minimize
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
sys.path.insert(0,str(ROOT/'research-20261016-w10-unconditional'))
import analytic_memory_probe as k
PAR=ROOT/'research-20261016/spectral-w10-refined-rational.json';DOC=json.loads(PAR.read_text());D=DOC['denominator']
OLD=[(i,j,F(a,D)) for i,j,a in DOC['a_upper'] if a];B=[F(b,D) for b in DOC['b_numerators']]
def construct(R):
    assert R>=9
    count=R-8;a={};b=[F(0)]*R
    for start in range(count):
        for i,j,w in OLD:a[i+start,j+start]=a.get((i+start,j+start),F(0))+w/count
        for i,w in enumerate(B):b[i+start]+=w/count
    for r in range(10,R+1):
        for i in range(R+1-r):a[i,i+r]=F(2,R+1-r)
    assert all(w>=0 for w in a.values()) and all(w>=0 for w in b)
    assert sum(b)==sum(B)
    totals=[sum(w for (i,j),w in a.items() if j-i==r) for r in range(1,R+1)]
    for r,total in enumerate(totals,1):
        assert total<=2
        if r<=9:assert total==sum(w for i,j,w in OLD if j-i==r)
        else:assert total==2
    pairs=list(a);weights=np.array([float(a[p]) for p in pairs]);bf=np.array(list(map(float,b)))
    inc=np.array([[float(i<=z<j) for z in range(R)] for i,j in pairs])
    def objective(x):
        amp,der=k.amplitude(inc@x)
        return float(bf@x+weights@(amp*amp)),bf+(2*weights*amp*der)@inc
    return objective,a,b,totals
def main():
    start=time.monotonic();rng=np.random.default_rng(2026101613);rows=[]
    for R in [10,12,16,24,32]:
        f,a,b,totals=construct(R)
        seeds=[np.resize([1.04168822,1.97157891],R),np.resize([1.97157891,1.04168822],R),
               np.full(R,2.0041),np.full(R,1.02)]
        seeds.extend(rng.choice([1.04,1.97,2.98],R,p=[.52,.46,.02]) for _ in range(16))
        fits=[minimize(f,s,jac=True,bounds=[(123/128,8)]*R,method='L-BFGS-B',
            options={'ftol':2e-15,'gtol':1e-10,'maxiter':1000}) for s in seeds]
        best=min(fits,key=lambda z:z.fun)
        row={'R':R,'window_point_count':R+1,'terms':len(a),'seed_count':len(seeds),
             'rank_totals_exact':list(map(str,totals)),'pressure_exact':str(sum(b)),
             'floating_feasible_upper_bound':float(best.fun),'gaps':best.x.tolist(),
             'gradient_inf_norm':float(max(abs(best.jac))),'global_minimum_certified':False,
             'implied_percent_if_this_were_a_global_floor':100*(.6721684105641189-float(sum(b)))/(1-best.fun)}
        rows.append(row);print(json.dumps(row),flush=True)
    out={'scope':__doc__,'parameter_sha256':hashlib.sha256(PAR.read_bytes()).hexdigest(),
         'results':rows,'seconds':time.monotonic()-start,'new_unconditional_zeta_bound_proven':False}
    (HERE/'global_tail_local_probe.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
if __name__=='__main__':main()
