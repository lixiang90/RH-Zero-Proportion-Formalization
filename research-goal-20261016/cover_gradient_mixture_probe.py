"""Finite actual-gradient convex-hull diagnostic, restricted to two frozen cells.

Every sampled point is rational and checked against all 45 DBM intervals.
HiGHS is discovery only.  A ten-point positive simplex, when found, is
rechecked using actual kernel interval gradients and a rational Neumann
perturbation estimate.  This diagnoses a convex first-order relaxation;
it neither constructs a stationary point nor proves a global energy floor.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from math import ceil, floor
import gzip, hashlib, json, time
import numpy as np
from scipy.optimize import linprog
import cover_phase_psd_obstruction as phase
import window_interval_kernel as ik

HERE=Path(__file__).parent; ROOT=HERE.parent; g=phase.g; SC=g.SC
PATHS=['r001000001000001101011101','r001000001000001110011100']
sha=lambda b:hashlib.sha256(b).hexdigest()
PAIR=np.array([[int(i<=k<j) for k in range(9)] for i,j,a in g.TERMS],dtype=float)
AW=np.array([a/g.D for i,j,a in g.TERMS]); BS=np.array(g.BS)/g.D


def feasible(point,state):
    return all(F(l)<=sum(point[i:j])<=F(u) for (i,j),l,u in zip(g.ALL,*state))


def vertex(state,coeff):
    closed=g.close(*state); assert closed is not None
    minimum,flow=g.minimize(0,coeff,closed[2]); dd=[r.copy() for r in closed[2]]
    for i,j,amount,u in flow['nonzero_flow']:
        if int(amount):dd[j][i]=min(dd[j][i],-int(u))
    for k in range(10):
        for i in range(10):
            for j in range(10):dd[i][j]=min(dd[i][j],dd[i][k]+dd[k][j])
    assert all(dd[k][k]>=0 for k in range(10))
    prefix=dd[0]; point=tuple(F(prefix[k+1]-prefix[k]) for k in range(9))
    assert feasible(point,state) and sum(c*x for c,x in zip(coeff,point))==minimum
    return point


def samples(state,seed):
    """32 exact objective vertices and 96 deterministic convex combinations."""
    rng=np.random.default_rng(seed); points=[]
    objectives=[]
    for k in range(9):
        for sign in [1,-1]:objectives.append([sign*int(i==k) for i in range(9)])
    objectives += [[int(x) for x in rng.integers(-1000000,1000001,9)] for _ in range(14)]
    vertices=[vertex(state,c) for c in objectives]
    def insert(p):
        assert feasible(p,state)
        if p not in points:points.append(p)
    for p in vertices:insert(p)
    insert(tuple(sum(p[k] for p in vertices)/len(vertices) for k in range(9)))
    # Include both broad edge mixtures and interior points without rejecting
    # points or drawing extra actual function evaluations.
    while len(points)<128:
        count=2 if len(points)%3==0 else (4 if len(points)%3==1 else 8)
        ids=rng.integers(0,len(vertices),count); weights=[int(x) for x in rng.integers(1,65537,count)]; total=sum(weights)
        insert(tuple(sum(F(w,total)*vertices[int(n)][k] for n,w in zip(ids,weights)) for k in range(9)))
    return points


def sincsecond(x):
    x=np.asarray(x,dtype=float); out=np.empty_like(x); small=abs(x)<1e-3; v=x[small]
    out[small]=-np.pi**2/3+np.pi**4*v*v/10-np.pi**6*v**4/168+np.pi**8*v**6/6480
    v=x[~small]; out[~small]=-np.pi*np.sin(np.pi*v)/v-2*np.cos(np.pi*v)/(v*v)+2*np.sin(np.pi*v)/(np.pi*v**3)
    return out


def evaluate(points):
    gs=np.array([[float(x/SC) for x in p] for p in points]); xs=gs@PAIR.T
    flat=xs.reshape(-1); plus=flat[:,None]+phase.freq; minus=flat[:,None]-phase.freq
    k=((np.sinc(plus)+np.sinc(minus))@phase.d)/(2*phase.Z)
    kp=((phase.sincprime(plus)+phase.sincprime(minus))@phase.d)/(2*phase.Z)
    kpp=((sincsecond(plus)+sincsecond(minus))@phase.d)/(2*phase.Z)
    w=(k*k).reshape(xs.shape); wp=(2*k*kp).reshape(xs.shape); wpp=(2*(kp*kp+k*kpp)).reshape(xs.shape)
    energy=gs@BS+w@AW; gradients=BS[None,:]+(wp*AW[None,:])@PAIR
    hessians=np.einsum('nt,ti,tj->nij',wpp*AW[None,:],PAIR,PAIR)
    return energy,gradients,hessians


def inverse(matrix):
    n=len(matrix); a=[list(row)+[F(int(i==j)) for j in range(n)] for i,row in enumerate(matrix)]
    for k in range(n):
        p=next(i for i in range(k,n) if a[i][k]);a[k],a[p]=a[p],a[k]
        z=a[k][k]; a[k]=[x/z for x in a[k]]
        for i in range(n):
            if i!=k:
                z=a[i][k]
                if z:a[i]=[x-z*y for x,y in zip(a[i],a[k])]
    return [r[n:] for r in a]


def rounded_interval(x,den=10**30):
    return F(floor(x.l*den),den),F(ceil(x.u*den),den)


@lru_cache(None)
def exact_w(x):return ik.w_jet(x,1)


def exact_point(point):
    energy=ik.I(sum(F(b,g.D)*x/SC for b,x in zip(g.BS,point)))
    gradient=[ik.I(F(b,g.D)) for b in g.BS]
    for i,j,a in g.TERMS:
        w,wp=exact_w(sum(point[i:j])/SC); energy+=F(a,g.D)*w
        for r in range(i,j):gradient[r]+=F(a,g.D)*wp
    return {'gradient_intervals':[[str(x) for x in rounded_interval(v)] for v in gradient],
      'energy_interval':[str(x) for x in rounded_interval(energy)]}


def robust_simplex(points,selected):
    if len(selected)!=10:return {'attempted':False,'reason':'The floating basic solution has other than ten supports.'}
    exact=[exact_point(points[n]) for n in selected]
    intervals=[[[F(v) for v in row] for row in p['gradient_intervals']] for p in exact]
    mids=[[(intervals[j][i][0]+intervals[j][i][1])/2 for j in range(10)] for i in range(9)]+[[F(1)]*10]
    radius=[[(intervals[j][i][1]-intervals[j][i][0])/2 for j in range(10)] for i in range(9)]+[[F(0)]*10]
    try: inv=inverse(mids)
    except StopIteration:return {'attempted':True,'passed':False,'reason':'Singular rational midpoint matrix.','points':exact}
    weights=[row[9] for row in inv]; eta=max(sum(sum(abs(inv[i][k])*radius[k][j] for k in range(10)) for j in range(10)) for i in range(10))
    delta=eta*max(map(abs,weights))/(1-eta) if eta<1 else None
    passed=delta is not None and min(weights)>delta
    # For the actual perturbed positive weights, payment for every possible
    # energy perturbation uses the same rigorous infinity-norm weight radius.
    average_energy=None
    if passed:
        elo=sum(w*F(p['energy_interval'][0]) for w,p in zip(weights,exact)); ehi=sum(w*F(p['energy_interval'][1]) for w,p in zip(weights,exact))
        payment=delta*sum(max(abs(F(x)) for x in p['energy_interval']) for p in exact)
        average_energy=[str(elo-payment),str(ehi+payment)]
    return {'attempted':True,'passed':bool(passed),'point_evidence':exact,
      'rational_midpoint_inverse':[[str(x) for x in row] for row in inv],'rational_midpoint_weights':[str(x) for x in weights],
      'eta_infinity_norm_bound':str(eta),'weight_error_infinity_bound':str(delta) if delta is not None else None,
      'minimum_midpoint_weight':str(min(weights)),'positive_weight_margin':str(min(weights)-delta) if delta is not None else None,
      'actual_mixture_energy_interval':average_energy,'actual_mixture_energy_below_floor':bool(average_energy and F(average_energy[1])<F(11,1250)),
      'analytic_interval_evaluation_Lean_proven':False,'ordinary_Lean_origin_in_hull_proof':False}


def diagnose(path,state,seed):
    pts=samples(state,seed); history=[]; result=None
    for count in [64,128]:
        energy,gradients,hessians=evaluate(pts[:count]); scale=np.max(abs(gradients),axis=0); scale=np.maximum(scale,1e-8)
        matrix=np.vstack([gradients.T/scale[:,None],np.ones(count)]); rhs=np.r_[np.zeros(9),1.]
        lp=linprog(energy,A_eq=matrix,b_eq=rhs,bounds=(0,None),method='highs',options={'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9})
        history.append({'sample_count':count,'LP_status':int(lp.status),'LP_message':lp.message,'LP_success':bool(lp.success)})
        if lp.success:result=(count,lp,energy,gradients,hessians);break
    if result is None:
        # This is only a finite-sample failure, not a separating bound over the cell.
        n=len(energy); a=np.vstack([np.c_[gradients.T,-np.eye(9)],np.c_[-gradients.T,-np.eye(9)]])
        closest=linprog(np.r_[np.zeros(n),np.ones(9)],A_ub=a,b_ub=np.zeros(18),
          A_eq=np.r_[np.ones(n),np.zeros(9)][None,:],b_eq=[1.],bounds=(0,None),method='highs')
        assert closest.success
        selected=np.where(closest.x[:n]>1e-10)[0].tolist(); weights=closest.x[selected]
        mean_gradient=weights@gradients[selected]; mean_hessian=np.einsum('n,nij->ij',weights,hessians[selected])
        direction=-closest.ineqlin.marginals[:9]+closest.ineqlin.marginals[9:]
        # A finite-sample hyperplane diagnostic.  It is not a uniform bound
        # on the nonlinear gradient graph between these sampled points.
        dots=gradients@direction
        nearest={'L1_gradient_residual_hint':float(closest.fun),'selected_indices':selected,'weights':weights.tolist(),
          'weighted_gradient_hint':mean_gradient.tolist(),'weighted_energy_hint':float(weights@energy[selected]),
          'weighted_energy_below_floor_hint':bool(weights@energy[selected]<.0088),
          'weighted_Hessian_minimum_eigenvalue_hint':float(np.linalg.eigvalsh(mean_hessian)[0]),
          'separating_direction_hint':direction.tolist(),'minimum_sample_directional_derivative_hint':float(min(dots)),
          'maximum_sample_directional_derivative_hint':float(max(dots)),
          'finite_sample_separation_is_not_whole_cell_separation':True}
        return {'path':path,'cell':state,'history':history,'sample_points_gap_units':[[str(x) for x in p] for p in pts],
          'sample_energies_hint':energy.tolist(),'sample_gradients_hint':gradients.tolist(),'origin_in_sampled_gradient_hull_hint':False,
          'nearest_gradient_mixture_hint':nearest,'whole_cell_gradient_separation_proven':False,
          'minimum_sample_energy_hint':float(min(energy)),'maximum_sample_energy_hint':float(max(energy)),
          'samples_at_or_below_floor':int(sum(energy<=.0088)),'evaluated_actual_points':len(pts),
          'all_coordinates_strictly_above_original_sep':all(v>g.SEP for v in state[0][:9])}
    count,lp,energy,gradients,hessians=result; selected=np.where(lp.x>1e-10)[0].tolist();weights=lp.x[selected]
    mixh=np.einsum('n,nij->ij',weights,hessians[selected]); robust=robust_simplex(pts,selected)
    return {'path':path,'cell':state,'history':history,'evaluated_actual_points':count,'origin_in_sampled_gradient_hull_hint':True,
      'sample_points_gap_units':[[str(x) for x in p] for p in pts[:count]],'sample_energies_hint':energy.tolist(),'sample_gradients_hint':gradients.tolist(),
      'sample_hessian_minimum_eigenvalues_hint':[float(np.linalg.eigvalsh(h)[0]) for h in hessians],
      'selected_indices':selected,'floating_weights':weights.tolist(),'selected_energies_hint':energy[selected].tolist(),
      'floating_mixture_energy_hint':float(weights@energy[selected]),'floating_mixture_below_floor_hint':bool(weights@energy[selected]<.0088),
      'floating_mixture_gradient_hint':(weights@gradients[selected]).tolist(),'floating_weighted_Hessian_hint':mixh.tolist(),
      'floating_weighted_Hessian_minimum_eigenvalue_hint':float(np.linalg.eigvalsh(mixh)[0]),'robust_simplex':robust,
      'all_coordinates_strictly_above_original_sep':all(v>g.SEP for v in state[0][:9]),
      'a_stationary_point_is_not_constructed':True}


def main():
    start=time.monotonic(); raw=(HERE/'cover-curvature-parent64.input.json.gz').read_bytes(); doc=json.loads(gzip.decompress(raw)); lookup={r['path']:r for r in doc['cases']}; rows=[]
    for n,path in enumerate(PATHS):
        row=diagnose(path,tuple(lookup[path]['before']),202610170+n); rows.append(row)
        print(json.dumps({'path':path,'sample_counts':[h['sample_count'] for h in row['history']],
          'hull_hint':row['origin_in_sampled_gradient_hull_hint'],'simplex_supports':len(row.get('selected_indices',[])),
          'robust_interval_simplex_passed':row.get('robust_simplex',{}).get('passed'),
          'average_energy_hint':row.get('floating_mixture_energy_hint'),'weighted_Hessian_min_eig_hint':row.get('floating_weighted_Hessian_minimum_eigenvalue_hint'),
          'seconds':time.monotonic()-start}),flush=True)
    receipt={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'input_sha256':sha(raw),
      'parameters_sha256':sha(ik.PARAM.read_bytes()),'kernel_interval_source_sha256':sha(Path(ik.__file__).read_bytes()),
      'interval_trig_source_sha256':sha(Path(ik.interval.__file__).read_bytes()),'cases':len(rows),'maximum_actual_points_per_case':128,
      'rational_interval_robust_simplex_passes':sum(bool(r.get('robust_simplex',{}).get('passed')) for r in rows),
      'new_cell_exclusions':0,'whole_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    out=HERE/'cover-gradient-mixture.json'; out.write_text(json.dumps({'receipt':receipt,'rows':rows},separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
