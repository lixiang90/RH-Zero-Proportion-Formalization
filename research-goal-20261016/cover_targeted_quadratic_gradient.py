"""Targeted six-cell gradient/Hessian diagnosis and total-quadratic bounds.

Floating optimizers select points/directions only. Quadratic upper estimates
use exact integer jets, signed total matrices, exact LDL and balanced flows.
Any successful certificate still requires separate independent replay.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,math,time
import numpy as np
from scipy.optimize import minimize,linprog,root,LinearConstraint
import cover_newwindow_gram as gram
import cover_correlated_curvature as curvature
g=gram.g;SC=g.SC;DS=curvature.DS;HERE=Path(__file__).parent

def psd_ldl(A):
    n=len(A);L=[[F(int(i==j)) for j in range(n)] for i in range(n)];D=[]
    for j in range(n):
        d=A[j][j]-sum(L[j][k]**2*D[k] for k in range(j));assert d>=0;D.append(d)
        for i in range(j+1,n):
            v=A[i][j]-sum(L[i][k]*L[j][k]*D[k] for k in range(j))
            if d:L[i][j]=v/d
            else:assert v==0
    assert all(A[i][j]==sum(L[i][k]*L[j][k]*D[k] for k in range(n)) for i in range(n) for j in range(n))
    return L,D

def scalar_data(state,oracle):
    data=[]
    for i,j,aw in g.TERMS:
        z=g.LOOK[i,j];l,u=state[0][z],state[1][z];P=l+u;r=F(u-l,2*SC)
        v,s=oracle.taylor.point(P);_,third=oracle.point(P);vals=[v,s,third];m=[round((z.l+z.u)*DS/2) for z in vals]
        e=[max(abs(z.l*DS-k),abs(z.u*DS-k)) for z,k in zip(vals,m)]
        err=curvature.ceil(e[0]+e[1]*r+e[2]*r*r/2+F(oracle.fourth_bound(l,u))*r**3/6)
        data.append([P,*m,err])
    return data

def quadratic_upper(state,data,d):
    C=8*SC*SC*DS*sum(b*v for b,v in zip(g.BS,d));E=0;coeff=[0]*9;Q=[[0]*9 for _ in range(9)]
    for (i,j,aw),(P,m0,m1,m2,err) in zip(g.TERMS,data):
        s=sum(d[i:j]);weight=aw*s;C+=weight*(8*SC*SC*m0-4*SC*m1*P+m2*P*P);E+=8*SC*SC*abs(weight)*err
        for k in range(i,j):
            coeff[k]+=weight*(8*SC*m1-4*m2*P)
            for z in range(i,j):Q[k][z]+=4*weight*m2
    q0=[F(state[0][k]+state[1][k],2) for k in range(9)];r=[F(state[1][k]-state[0][k],2) for k in range(9)]
    active=[i for i in range(9) if r[i]];M=[[r[i]*Q[i][j]*r[j] for j in active] for i in active]
    scale=max([abs(x) for row in M for x in row]+[F(1)]);matrix=np.array([[float(x/scale) for x in row] for row in M])
    ev=float(np.linalg.eigvalsh(matrix)[-1]) if active else 0.;t=math.ceil((max(ev,0)+1e-12)*float(scale)) if ev>=0 else 0
    for attempt in range(4):
        try:L,D=psd_ldl([[F(t if i==j else 0)-M[i][j] for j in range(len(active))] for i in range(len(active))]);break
        except AssertionError:t+=max(1,math.ceil(float(scale)*1e-10))
    else:
        t=max([F(0)]+[M[i][i]+sum(abs(M[i][j]) for j in range(len(active)) if i!=j) for i in range(len(active))]);t=curvature.ceil(t)
        L,D=psd_ldl([[F(t if i==j else 0)-M[i][j] for j in range(len(active))] for i in range(len(active))])
    linear=[F(coeff[i])+2*sum(Q[i][j]*q0[j] for j in range(9)) for i in range(9)];assert all(v.denominator==1 for v in linear)
    constant=F(C)-sum(q0[i]*Q[i][j]*q0[j] for i in range(9) for j in range(9));assert constant.denominator==1
    cl=g.close(*state);minimum,flow=g.minimize(0,[-int(v) for v in linear],cl[2]);upper=constant+E+len(active)*t-minimum
    cert={'direction':d,'scalar_quadratic_data':[[P,str(m0),str(m1),str(m2),str(err)] for P,m0,m1,m2,err in data],
      'constant':str(C),'error':str(E),'linear_coefficient':list(map(str,coeff)),'total_quadratic_matrix':[[str(v) for v in row] for row in Q],
      'scaled_matrix_shift':str(t),'PSD_L':[[str(v) for v in row] for row in L],'PSD_D':list(map(str,D)),
      'affine_coefficient':list(map(str,linear)),'affine_constant':str(constant),'quadratic_payment':str(len(active)*t),
      'negative_maximum':str(minimum),'flow':flow,'upper_numerator':str(upper),'denominator':str(8*SC*SC*g.D*DS)}
    return float(upper/(8*SC*SC*g.D*DS)),cert

def main():
    start=time.monotonic();raw=(HERE/'cover-current-frontier-20261017b.json').read_bytes();doc=json.loads(raw)
    inputs=[r for r in doc['frontier'] if r['depth']>=18];assert len(inputs)==6
    S=np.zeros((len(g.TERMS),9));SA=np.zeros((45,9));weights=np.array([aw/g.D for i,j,aw in g.TERMS]);bs=np.array(g.BS)/g.D
    for t,(i,j,aw) in enumerate(g.TERMS):S[t,i:j]=1
    for t,(i,j) in enumerate(g.ALL):SA[t,i:j]=1
    def value(x):return float(bs@x+weights@gram.w_value_derivative(S@x)[0])
    def grad(x):return bs+S.T@(weights*gram.w_value_derivative(S@x)[1])
    def hessian(x):
        y=(S@x)[:,None];freq=gram.w.FREQ;coef=gram.w.COEFF;normal=gram.w.NORM
        def sinc2(z):
            out=np.empty_like(z);small=abs(z)<.001;v=z[small]
            out[small]=-np.pi**2/3+np.pi**4*v*v/10-np.pi**6*v**4/168+np.pi**8*v**6/6480
            v=z[~small];out[~small]=-np.pi*np.sin(np.pi*v)/v-2*np.cos(np.pi*v)/v**2+2*np.sin(np.pi*v)/(np.pi*v**3)
            return out
        k=((np.sinc(y+freq)+np.sinc(y-freq))@coef)/(2*normal)
        d=((gram.sinc_derivative(y+freq)+gram.sinc_derivative(y-freq))@coef)/(2*normal)
        d2=((sinc2(y+freq)+sinc2(y-freq))@coef)/(2*normal);v=2*(d*d+k*d2)
        return S.T@np.diag(weights*v)@S
    oracle=curvature.CurvatureOracle(curvature.first.TaylorOracle(HERE/'cover_newjet.json'));rows=[];accepted=0
    for case in inputs:
        state=(case['state'][0],case['state'][1]);lo=np.array(state[0])/SC;hi=np.array(state[1])/SC;constraints=LinearConstraint(SA,lo,hi)
        lp=linprog(np.zeros(9),A_ub=np.r_[SA,-SA],b_ub=np.r_[hi,-lo],bounds=[(None,None)]*9,method='highs');assert lp.success
        q0=np.array([(state[0][i]+state[1][i])/(2*SC) for i in range(9)]);seed=lp.x
        fit=minimize(value,seed,jac=grad,constraints=constraints,method='SLSQP',options={'ftol':1e-14,'maxiter':500})
        station=minimize(lambda x:float(grad(x)@grad(x)/2),fit.x,jac=lambda x:hessian(x)@grad(x),constraints=constraints,method='SLSQP',options={'ftol':1e-22,'maxiter':500})
        rootfit=root(grad,station.x,jac=hessian,tol=1e-10);free=[i for i in range(9) if state[0][i]>g.SEP]
        directions=set()
        for k in range(9):
            d=[0]*9;d[k]=1;directions.add(tuple(d))
            if k in free:d[k]=-1;directions.add(tuple(d))
        for v in [rootfit.x-q0,-grad(station.x),-grad(q0)]:
            v=np.array(v);v[[i for i in range(9) if i not in free]]=np.maximum(v[[i for i in range(9) if i not in free]],0)
            if max(abs(v))>0:directions.add(tuple(round(z/max(abs(v))*65536) for z in v))
        data=scalar_data(state,oracle);affine=[oracle.taylor.affine(state[0][g.LOOK[i,j]],state[1][g.LOOK[i,j]]) for i,j,aw in g.TERMS]
        best=None;linear_best=float('inf');t0=time.monotonic()
        for d in sorted(directions):
            bound,cert=quadratic_upper(state,data,list(d));normal=max(abs(v) for v in d)
            if best is None or bound/normal<best[0]:best=(bound/normal,cert)
            lin,_=curvature.first.exact_upper(state,affine,list(d));linear_best=min(linear_best,lin/(2*SC*g.D*DS*normal))
        curvature_data=[oracle.affine(state[0][g.LOOK[i,j]],state[1][g.LOOK[i,j]]) for i,j,aw in g.TERMS]
        curvature_result=None
        for point in [station.x,rootfit.x,fit.x]:
            if not free:break
            values,vectors=np.linalg.eigh(hessian(point)[np.ix_(free,free)])
            for col,ev in enumerate(values):
                if ev>=-1e-10:break
                for den in [16,65536]:
                    v=vectors[:,col];d=[0]*9
                    for k,i in enumerate(free):d[i]=round(v[k]/max(abs(v))*den)
                    upper,flow=curvature.exact_upper(state,curvature_data,d)
                    if upper<0:
                        curvature_result={'kind':'correlated_negative_curvature','direction':d,'direction_scale':den,
                          'upper_numerator':str(upper),'denominator':str(2*SC*g.D*DS),'eigenvalue_hint':float(ev),
                          'scalar_affine_data':[[P,str(m0),str(m1),str(err),kind] for P,m0,m1,err,kind in curvature_data],
                          'exact_flow':flow,'affine_terms':sum(v[4]=='affine' for v in curvature_data)};break
                if curvature_result:break
            if curvature_result:break
        def diagnostic(x):
            H=hessian(x);return {'point':list(map(float,x)),'energy_hint':value(x),'gradient_infinity_hint':float(max(abs(grad(x)))),
              'Hessian_min_eigenvalue_hint':float(np.linalg.eigvalsh(H)[0]),'free_block_min_eigenvalue_hint':float(np.linalg.eigvalsh(H[np.ix_(free,free)])[0]) if free else None,
              'inside_cell_hint':bool(np.all(SA@x>=lo-1e-8) and np.all(SA@x<=hi+1e-8))}
        accepted+=best[0]<0
        bcert=best[1];dn=max(abs(v) for v in bcert['direction']);normalizer=int(bcert['denominator'])*dn
        rows.append({'path':case['path'],'depth':case['depth'],'free_coordinates':free,'constrained_energy_minimum_hint':diagnostic(fit.x),
          'constrained_smallest_gradient_hint':diagnostic(station.x),'root_hint':diagnostic(rootfit.x),'root_solver_success':bool(rootfit.success),
          'energy_solver_success':bool(fit.success),'energy_solver_message':str(fit.message),
          'gradient_solver_success':bool(station.success),'gradient_solver_message':str(station.message),
          'best_linear_upper_per_direction_unit':linear_best,'best_quadratic_upper_per_direction_unit':best[0],
          'best_quadratic_error_payment_per_unit':int(bcert['error'])/normalizer,
          'best_quadratic_matrix_payment_per_unit':int(bcert['quadratic_payment'])/normalizer,
          'candidate_directions':len(directions),'bound_seconds':time.monotonic()-t0,'quadratic_candidate_certificate':best[1] if best[0]<0 else None,
          'uniform_negative_curvature_certificate':curvature_result})
        print(json.dumps({'done':len(rows),'best_linear':linear_best,'best_quadratic':best[0],'new_candidates':accepted,'seconds':time.monotonic()-start}),flush=True)
    out={'scope':__doc__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'snapshot_sha256':hashlib.sha256(raw).hexdigest(),
      'cells':6,'negative_quadratic_upper_candidates':accepted,'uniform_negative_curvature_candidates':sum(bool(r['uniform_negative_curvature_certificate']) for r in rows),
      'independent_quadratic_replay_passed':False,'results':rows,
      'global_cover_complete':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    (HERE/'cover-targeted-quadratic-gradient.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps({k:v for k,v in out.items() if k!='results'}),flush=True)
if __name__=='__main__':main()
