"""Small phase-relaxation challenge; no lower bound or new theorem is claimed.

Eight frozen residual cells compare the old pointwise lower bound with
rank-one feasible upper witnesses for a deliberately weaker frozen-amplitude
phase relaxation.  The first cell also retains the old g/derivative graph
primal and its actual linked phases, and tests whether separate uniform
coefficient payments already admit that false KKT point.  Coefficient
variation samples are diagnostic lower estimates of required payments,
not rigorous uniform upper bounds.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
import gzip,hashlib,json,time
import numpy as np
from scipy.optimize import minimize
import cover_lifted_graph_probe as old_graph
HERE=Path(__file__).parent;ROOT=HERE.parent;g=old_graph.g;SC=g.SC
sha=lambda b:hashlib.sha256(b).hexdigest()
PARAM=ROOT/'research-20261016-followup/window_reweight_rational.json'
params=json.loads(PARAM.read_bytes());d=np.r_[1.,np.array(params['window_coefficient_numerators_1e9'])/1e9]
theta=np.sqrt(2)/2;Z=np.sin(theta)/theta;freq=np.r_[theta/np.pi,np.arange(1,25)]
ii=np.array([i for i,j,aw in g.TERMS]);jj=np.array([j for i,j,aw in g.TERMS]);aw=np.array([a/g.D for i,j,a in g.TERMS])


def sincprime(x):
    x=np.asarray(x,dtype=float);answer=np.empty_like(x);small=abs(x)<1e-4;v=x[small]
    answer[small]=-np.pi**2*v/3+np.pi**4*v**3/30-np.pi**6*v**5/840
    v=x[~small];answer[~small]=(np.pi*v*np.cos(np.pi*v)-np.sin(np.pi*v))/(np.pi*v*v)
    return answer


def coefficients(xs):
    x=np.atleast_1d(np.asarray(xs,dtype=float));plus=x[:,None]+freq;minus=x[:,None]-freq
    k=((np.sinc(plus)+np.sinc(minus))@d)/(2*Z);kp=((sincprime(plus)+sincprime(minus))@d)/(2*Z)
    den=np.pi**2*x*x-theta**2;A=np.cos(theta)*np.pi*x/(Z*den)
    Ap=np.cos(theta)*np.pi*(-np.pi**2*x*x-theta**2)/(Z*den*den)
    B=1/(1-2*np.pi**2*x*x);Bp=4*np.pi**2*x/(1-2*np.pi**2*x*x)**2
    sn=np.sin(np.pi*x);cs=np.cos(np.pi*x);C=k-A*sn-B*cs
    Cp=kp-Ap*sn-np.pi*A*cs-Bp*cs+np.pi*B*sn
    c0=C*C+(A*A+B*B)/2;c1=2*C*B;s1=2*C*A;c2=(B*B-A*A)/2;s2=A*B
    c0p=2*C*Cp+A*Ap+B*Bp;c1p=2*(Cp*B+C*Bp);s1p=2*(Cp*A+C*Ap);c2p=B*Bp-A*Ap;s2p=Ap*B+A*Bp
    value=np.array([c0,c1,s1,c2,s2]).T
    deriv=np.array([c0p,c1p+np.pi*s1,s1p-np.pi*c1,c2p+2*np.pi*s2,s2p-2*np.pi*c2]).T
    return value,deriv,np.array([A,B,C,Ap,Bp,Cp]).T


def pressure_primal(state):
    cl=g.close(*state);assert cl is not None and cl[:2]==state;minimum,flow=g.minimize(0,g.BS,cl[2]);dd=[r.copy() for r in cl[2]]
    for i,j,amount,u in flow['nonzero_flow']:
        if int(amount):dd[j][i]=min(dd[j][i],-u)
    for k in range(10):
        for i in range(10):
            for j in range(10):dd[i][j]=min(dd[i][j],dd[i][k]+dd[k][j])
    assert all(dd[k][k]>=0 for k in range(10));prefix=dd[0];gaps=[prefix[k+1]-prefix[k] for k in range(9)]
    assert all(l<=sum(gaps[i:j])<=u for (i,j),l,u in zip(g.ALL,*state)) and sum(b*x for b,x in zip(g.BS,gaps))==minimum
    return F(minimum,SC*g.D),gaps,flow


def energy(angles,q1,q2,linked):
    first=np.r_[0.,angles[:9]];second=2*first if linked else np.r_[0.,angles[9:]]
    z1=q1*np.exp(1j*(first[jj]-first[ii]));z2=q2*np.exp(1j*(second[jj]-second[ii]));value=float(aw@(z1.real+z2.real))
    grad1=np.zeros(10);grad2=np.zeros(10)
    np.add.at(grad1,ii,aw*z1.imag);np.add.at(grad1,jj,-aw*z1.imag)
    np.add.at(grad2,ii,aw*z2.imag);np.add.at(grad2,jj,-aw*z2.imag)
    return value,(grad1+2*grad2)[1:] if linked else np.r_[grad1[1:],grad2[1:]]


def phase_upper(value,prefix,linked,seed):
    q1=value[:,1]-1j*value[:,2];q2=value[:,3]-1j*value[:,4];rng=np.random.default_rng(seed)
    starts=[np.pi*prefix[1:],np.zeros(9),np.arange(1,10)*np.pi,np.arange(1,10)*1.04*np.pi]+[rng.uniform(-np.pi,np.pi,9) for _ in range(4)]
    if not linked:starts=[np.r_[s,2*s] for s in starts[:4]]+[rng.uniform(-np.pi,np.pi,18) for _ in range(4)]
    best=None
    for initial in starts:
        r=minimize(lambda x:energy(x,q1,q2,linked),initial,jac=True,method='BFGS',options={'gtol':1e-10,'maxiter':300})
        if best is None or r.fun<best.fun:best=r
    H1=np.zeros((10,10),dtype=complex);H2=H1.copy()
    H1[ii,jj]=aw*q1/2;H2[ii,jj]=aw*q2/2;H1=H1+H1.conj().T;H2=H2+H2.conj().T
    return {'pair_energy_primal_upper_hint':float(aw@value[:,0])+float(best.fun),'angles':list(map(float,best.x)),
      'optimizer_success':bool(best.success),'eigenvalue_dual_lower_hint':float(aw@value[:,0])+10*(float(np.linalg.eigvalsh(H1)[0])+float(np.linalg.eigvalsh(H2)[0]))}


def first_cell_graph_payment(state,taylor,oracle,center_value,center_deriv):
    result,stats,lp=old_graph.solve(state,taylor,oracle,True);assert result is None and lp.success and lp.fun<=1e-10
    gaps=lp.x[:9];u=lp.x[9:9+len(g.TERMS)];positions=np.r_[0.,np.cumsum(gaps)];x=positions[jj]-positions[ii]
    angles=np.pi*x;basis=np.array([np.ones(len(x)),np.cos(angles),np.sin(angles),np.cos(2*angles),np.sin(2*angles)]).T
    center_prediction=np.sum(center_deriv*basis,axis=1);rows=[]
    for t,(i,j,weight) in enumerate(g.TERMS):
        z=g.LOOK[i,j];l,hi=state[0][z]/SC,state[1][z]/SC
        samples=np.unique(np.r_[l,hi,np.arange(np.ceil(l*64),np.floor(hi*64)+1)/64])
        _,var,_=coefficients(samples);lower=np.max(abs(var-center_deriv[t]),axis=0);epsilon=float(sum(lower));needed=abs(float(u[t])-float(center_prediction[t]))
        rows.append({'term':t,'span':x[t],'old_graph_derivative':float(u[t]),'frozen_phase_prediction':float(center_prediction[t]),
          'required_scalar_payment_at_primal':needed,'sampled_lower_estimates_of_component_suprema':list(map(float,lower)),
          'sampled_separate_l1_payment_lower_estimate':epsilon,'slack':epsilon-needed,'samples':len(samples)})
    gradients=np.array(g.BS,dtype=float)/g.D
    for t,(i,j,weight) in enumerate(g.TERMS):gradients[i:j]+=weight/g.D*u[t]
    strict=[i for i in range(9) if state[0][i]>g.SEP]
    residual=max([abs(gradients[i]) for i in strict]+[max(0.,-gradients[i]) for i in range(9) if i not in strict])
    return {'scope':'Old graph primal retained; phases are its actual linked position phases, so all arcs and edge Toeplitz links hold.',
      'old_graph_L1_residual_hint':float(lp.fun),'direct_KKT_residual_hint':float(residual),'gap_primal':list(map(float,gaps)),
      'all_graph_derivatives_fit_sampled_separate_uniform_payments':all(r['slack']>=-1e-10 for r in rows),
      'minimum_slack':min(r['slack'] for r in rows),'failed_terms':[r['term'] for r in rows if r['slack']<-1e-10],
      'payments_are_not_uniform_upper_bounds':True,'rank_one_Gram_layers_linked':True,'old_graph_and_cell_geometry_retained':True,'rows':rows}


def main():
    start=time.monotonic();packed=(HERE/'cover-curvature-parent64.input.json.gz').read_bytes();source=json.loads(gzip.decompress(packed));cases={r['path']:r for r in source['cases']}
    selectionraw=(HERE/'cover-lifted-graph-energy8.json').read_bytes();selection=json.loads(selectionraw);assert selection['receipt']['input_sha256']==sha(packed)
    taylor=old_graph.context.curvature.first.TaylorOracle(HERE/'cover_newjet.json');oracle=old_graph.GraphOracle(HERE/'cover_newjet.json');rows=[]
    for number,selected in enumerate(selection['rows']):
        path=selected['path'];state=tuple(cases[path]['before']);prefix2=np.r_[0.,[state[0][g.LOOK[0,j]]+state[1][g.LOOK[0,j]] for j in range(1,10)]]
        prefix=prefix2/(2*SC);xs=prefix[jj]-prefix[ii];value,deriv,amp=coefficients(xs);pressure,gp,pf=pressure_primal(state)
        independent=phase_upper(value,prefix,False,100+number);linked=phase_upper(value,prefix,True,200+number)
        old=old_graph.context.w.certify(state);oldfloor=int(old.get('floor_numerator','-1'))/g.DEN
        check=first_cell_graph_payment(state,taylor,oracle,value,deriv) if number==0 else None
        row={'path':path,'frozen_span_points':list(map(float,xs)),'value_coefficients':value.tolist(),'derivative_coefficients':deriv.tolist(),
          'minimum_pressure':str(pressure),'pressure_primal_gap_units':gp,'pressure_flow':pf,'old_pointwise_lower_bound':oldfloor,
          'independent_phase':independent,'linked_phase':linked,'weak_frozen_model_primal_upper_hint':float(pressure)+independent['pair_energy_primal_upper_hint'],
          'linked_frozen_model_primal_upper_hint':float(pressure)+linked['pair_energy_primal_upper_hint'],
          'weak_value_phase_geometry_links_retained':False,'weak_value_old_graph_constraints_retained':False,'first_cell_old_graph_payment':check}
        rows.append(row);print(json.dumps({'cases':len(rows),'old_floor':oldfloor,'independent_upper':row['weak_frozen_model_primal_upper_hint'],
          'linked_upper':row['linked_frozen_model_primal_upper_hint'],'first_payment_fits':check and check['all_graph_derivatives_fit_sampled_separate_uniform_payments'],
          'seconds':time.monotonic()-start}),flush=True)
    out={'receipt':{'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'input_sha256':sha(packed),'selection_sha256':sha(selectionraw),'parameter_sha256':sha(PARAM.read_bytes()),
      'cases':8,'strict_PSD_dual_lower_bounds':0,'uniform_coefficient_upper_bounds_proven':False,'new_lower_bound_proven':False,
      'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start},'rows':rows}
    (HERE/'cover-phase-psd-obstruction.json').write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(out['receipt']),flush=True)
if __name__=='__main__':main()
