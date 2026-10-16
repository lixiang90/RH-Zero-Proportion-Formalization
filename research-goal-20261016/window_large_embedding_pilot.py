"""One larger-block transfer from the unconditional old nine-point floor.

All nine-point subsets of seventeen ordered vertices are considered, modulo
translation. No new analytic floor or multivariate cover is assumed. A fixed
sixteen-row LP selects nonnegative embeddings; exact arithmetic checks the
candidate and a rounded/repaired dual bound. No Lean is launched here.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from math import lcm, ceil
import hashlib,json,time
import numpy as np
from scipy.optimize import linprog
from window_kernel_floor_transfer_design import parse_old,LOCAL,FINAL,SITE

HERE=Path(__file__).resolve().parent
OUT=HERE/'window-large-embedding-pilot.json'
N=17
H=F(6721684105641188747759983512104999330646,10**40)
WEBSITE=F(34191001116882886388531117129201664,50760020691785094633026544189453125)
TARGET=WEBSITE+F(1,100000)

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def columns(old):
    den=lcm(*[v.denominator for v in list(old['a'].values())+old['b']])
    edges=[(i,j,int(a*den)) for (i,j),a in old['a'].items()]
    pressure=[int(v*den) for v in old['b']]
    for tail in combinations(range(1,N),8):
        vertices=(0,)+tail
        ranks=[0]*(N-1)
        for i,j,a in edges:ranks[vertices[j]-vertices[i]-1]+=a
        b=sum(pressure[i]*(vertices[i+1]-vertices[i]) for i in range(8))
        yield vertices,ranks,b,den

def main():
    assert not OUT.exists();started=time.monotonic()
    watched=[Path(__file__),LOCAL,FINAL,SITE,HERE/'window_kernel_floor_transfer_design.py']
    guards={str(p.relative_to(HERE.parent)):sha(p) for p in watched}
    old=parse_old(LOCAL);cols=list(columns(old));den=cols[0][3]
    assert len(cols)==12870 and all(c[3]==den for c in cols)
    A=np.array([[r[i]/den for _,r,_,_ in cols] for i in range(N-1)])
    objective=np.array([float(TARGET*old['c']-F(b,den)) for _,_,b,_ in cols])
    fit=linprog(-objective,A_ub=A,b_ub=np.full(N-1,2.),bounds=(0,None),
        method='highs-ipm',options={'time_limit':45.})
    mass=sum(old['a'].values());sum_upper=2*(N-1)/mass
    assert old['c']*sum_upper<1
    out={'scope':__doc__,'inputs_sha256':guards,'vertices':N,
         'translation_classes':len(cols),'old_floor':str(old['c']),
         'H':str(H),'target':str(TARGET),'all_columns_pair_mass':str(mass),
         'all_feasible_weight_sum_upper':str(sum_upper),
         'all_feasible_denominators_positive_exact':True,
         'LP_status':int(fit.status),'LP_message':str(fit.message),
         'solver_calls':1,'new_floor_formalized':False,'new_zero_proportion_proven':False}
    if fit.success:
        selected=[(i,F(str(float(v)))) for i,v in enumerate(fit.x) if v>0]
        exact_masses=[sum(F(cols[i][1][r],den)*v for i,v in selected) for r in range(N-1)]
        down=max([F(1)]+[m/2 for m in exact_masses])
        selected=[(i,v/down) for i,v in selected]
        exact_masses=[sum(F(cols[i][1][r],den)*v for i,v in selected) for r in range(N-1)]
        assert all(0<=v for _,v in selected) and all(m<=2 for m in exact_masses)
        floor=old['c']*sum(v for _,v in selected)
        B=sum(F(cols[i][2],den)*v for i,v in selected)
        ratio=(H-B)/(1-floor)
        scale=10**15
        dual=[F(max(0,ceil(float(-v)*scale)),scale) for v in fit.ineqlin.marginals]
        repair=max([F(0)]+[(TARGET*old['c']-F(b,den)-sum(F(r,den)*y for r,y in zip(ranks,dual)))/mass
                                for _,ranks,b,_ in cols])
        dual=[y+repair for y in dual]
        slacks=[sum(F(r,den)*y for r,y in zip(ranks,dual))-(TARGET*old['c']-F(b,den))
                for _,ranks,b,_ in cols]
        assert min(slacks)>=0
        upper=2*sum(dual);needed=TARGET-H
        out.update({'selected':[{'vertices':list(cols[i][0]),'weight':str(v)} for i,v in selected],
            'capacity_rescale':str(down),'exact_rank_masses':list(map(str,exact_masses)),
            'exact_floor_by_embedding':str(floor),'exact_pressure':str(B),
            'exact_ratio_formula':str(ratio),'ratio_percent_hint':float(100*ratio),
            'exact_candidate_exceeds_target':ratio>TARGET,
            'exact_dual':list(map(str,dual)),'dual_repair':str(repair),
            'dual_min_column_slack':str(min(slacks)),'dual_objective_upper':str(upper),
            'required_objective':str(needed),'exact_dual_shortfall':str(needed-upper),
            'construction_class_excluded_exact':upper<needed,
            'LP_objective_hint':float(-fit.fun),'LP_iterations':int(fit.nit)})
    assert guards=={str(p.relative_to(HERE.parent)):sha(p) for p in watched}
    out['all_inputs_unchanged']=True;out['seconds']=time.monotonic()-started
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:out[k] for k in ['vertices','translation_classes','LP_status','ratio_percent_hint',
          'exact_candidate_exceeds_target','construction_class_excluded_exact','seconds'] if k in out}),flush=True)

if __name__=='__main__':main()
