"""Deterministic boundary-risk diagnostic for five fixed lattice chambers.

One LP-projected start per facet, followed by one constrained floating
minimization. The task is limited to five patterns x39 weighted spans x2.
The absence of a found counterexample cannot prove phase concentration.
Facet/pressure feasibility is checked numerically, not certified by Lean.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,time
import numpy as np
from scipy.optimize import linprog,minimize,LinearConstraint
import analytic_memory_probe as m

HERE=Path(__file__).parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    start=time.monotonic();source=HERE/'analytic_gram_wide_adaptive.json'
    watched=[source,m.PARAM,Path(__file__),HERE/'analytic_memory_probe.py']
    initial={str(p.name):sha(p) for p in watched};data=json.loads(source.read_text())
    chosen=sorted(data['results'],key=lambda r:F(r['Gram_lower_bound_exact']))[:5]
    radius=.49;target=.00866;rows=[]
    for pattern_index,pattern in enumerate(chosen):
        n=np.array(pattern['integer_gaps']);anchor=np.array(pattern['anchor_numerators'])/pattern['anchor_denominator']
        centers=m.INC@n;lo=centers-radius;hi=centers+radius
        A=np.vstack([m.INC,-m.INC,m.B[None,:]])
        rhs=np.r_[hi,-lo,target]
        # L-infinity projection gives a deterministic near-anchor feasible seed.
        lpA=np.vstack([np.c_[A,np.zeros(len(A))],np.c_[np.eye(9),-np.ones(9)],np.c_[-np.eye(9),-np.ones(9)]])
        lpb=np.r_[rhs,anchor,-anchor]
        for k,(i,j,a) in enumerate(m.TERMS):
            for sign in [-1,1]:
                facet=float(centers[k]+sign*radius);eq=m.INC[k]
                lp=linprog(np.r_[np.zeros(9),1.],A_ub=lpA,b_ub=lpb,A_eq=np.c_[eq[None,:],np.zeros(1)],b_eq=[facet],
                    bounds=[(.85,None)]*9+[(0,None)],method='highs')
                row={'pattern_index':pattern_index,'integer_gaps':n.tolist(),'facet_pair':[i,j],
                    'facet_sign':sign,'facet_value':facet,'floating_lp_feasible':bool(lp.success)}
                if not lp.success:
                    row['lp_status']=int(lp.status);row['lp_message']=lp.message;rows.append(row);continue
                seed=lp.x[:9]
                constraint=LinearConstraint(A,np.full(len(A),-np.inf),rhs)
                equality=LinearConstraint(eq[None,:],[facet],[facet])
                fit=minimize(lambda x:m.objective(x,9),seed,jac=True,bounds=[(.85,None)]*9,
                    constraints=[constraint,equality],method='SLSQP',
                    options={'maxiter':300,'ftol':5e-14,'disp':False})
                value,grad=m.objective(fit.x,9)
                ineq=max(float(np.max(A@fit.x-rhs)),float(.85-np.min(fit.x)),0.)
                equality_residual=abs(float(eq@fit.x-facet));violation=max(ineq,equality_residual)
                row.update({'floating_optimizer_success':bool(fit.success),'optimizer_message':str(fit.message),
                    'iterations':int(fit.nit),'seed_gaps':seed.tolist(),'gaps':fit.x.tolist(),
                    'original_full_F_float':value,'weighted_pressure_float':float(m.B@fit.x),
                    'max_linear_violation_float':ineq,'facet_equality_residual_float':equality_residual,
                    'feasible_within_1e_8':violation<=1e-8,'below_candidate_floor_float':value<target,
                    'floating_Gram_bound_for_this_chamber':pattern['Gram_lower_bound_float']})
                rows.append(row)
        done=[r for r in rows if r['pattern_index']==pattern_index and r.get('feasible_within_1e_8')]
        print(json.dumps({'pattern_index':pattern_index,'completed':len(rows),'feasible_facets':len(done),
            'min_original_F':min((r['original_full_F_float'] for r in done),default=None)}),flush=True)
    final={str(p.name):sha(p) for p in watched};assert initial==final
    feasible=[r for r in rows if r.get('feasible_within_1e_8')]
    result={'scope':__doc__,'input_sha256_start':initial,'input_sha256_end':final,'all_inputs_unchanged':True,
        'patterns':len(chosen),'facet_tasks':len(rows),'floating_lp_feasible_tasks':sum(r['floating_lp_feasible'] for r in rows),
        'numerically_feasible_tasks_within_1e_8':len(feasible),
        'minimum_feasible_original_F_float':min((r['original_full_F_float'] for r in feasible),default=None),
        'found_numerically_feasible_below_candidate_floor':sum(r['below_candidate_floor_float'] for r in feasible),
        'results':rows,'seconds':time.monotonic()-start,
        'phase_concentration_proven':False,'new_unconditional_bound_proven':False}
    (HERE/'analytic_boundary_probe.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in result.items() if k!='results'}),flush=True)

if __name__=='__main__':main()
