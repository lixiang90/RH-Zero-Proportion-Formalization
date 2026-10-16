"""Floating exploration of unused rank > 9 interactions.

The Poisson identity gives a finite Fourier expression for the infinite
periodic energy, but numerical quadrature/optimization here are discovery
only. No lower bound for arbitrary separated chains is asserted.
"""
from pathlib import Path
import hashlib,json,sys,time
import numpy as np
from scipy.optimize import minimize
from scipy.integrate import quad
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
sys.path.insert(0,str(ROOT/'research-20261016-w10-unconditional'))
import analytic_memory_probe as k
PAR=ROOT/'research-20261016/spectral-w10-refined-rational.json'
DOC=json.loads(PAR.read_text());D=DOC['denominator'];B=sum(DOC['b_numerators'])/D
RANK9=np.array([sum(a/D for i,j,a in DOC['a_upper'] if j-i==r) for r in range(1,10)])
def incidence(m,R):
    inc=np.zeros((R*m,m))
    for r in range(1,R+1):
        for i in range(m):
            for j in range(m):inc[(r-1)*m+i,j]=r//m
            for j in range(r%m):inc[(r-1)*m+i,(i+j)%m]+=1
    return inc
def objective(m,R):
    inc=incidence(m,R);weights=np.repeat(np.r_[RANK9[:min(R,9)],np.full(max(R-9,0),2.)]/m,m)
    def f(x):
        z=inc@x;v,dv=k.amplitude(z)
        return float(B*np.mean(x)+weights@(v*v)),np.full(m,B/m)+(weights*2*v*dv)@inc
    return f
def profile(x):return np.cos(2*np.pi*x*k.FREQ)@k.COEF
def hhat(x):
    x=abs(x)
    if x>=1:return 0.
    return quad(lambda s:profile(s)*profile(x-s),x-.5,.5,epsabs=1e-13,epsrel=1e-13)[0]/k.NORM**2
def poisson(g):
    m=len(g);L=sum(g);y=np.r_[0.,np.cumsum(g[:-1])]
    val=hhat(0)*m*m
    parts=[]
    for n in range(1,int(np.ceil(L))):
        term=2*hhat(n/L)*abs(np.exp(2j*np.pi*n*y/L).sum())**2
        val+=term;parts.append([n,term/(m*L)])
    # Poisson includes the diagonal and both directions at all positive ranks.
    E=val/(m*L)-1+B*L/m
    # Preserve the tiny exact-parameter rank deficits for r <= 9.
    inc=incidence(m,9);amp,_=k.amplitude(inc@np.array(g));corr=np.repeat((RANK9-2)/m,m)@(amp*amp)
    return float(E+corr),parts
def main():
    start=time.monotonic();old=json.loads((HERE/'global_periodic.json').read_text())
    rows=[]
    for m in [1,2,3]:
        initial=next(r['gaps'] for r in old['results'] if r['period']==m)
        seeds=[np.array(initial),np.full(m,2.0041069254070067),np.full(m,1.02)]
        if m==2:seeds+=[np.array([1.04,1.97]),np.array([1.0,3.0])]
        if m==3:seeds+=[np.array([1.03,1.03,1.96]),np.array([1.0,2.,2.])]
        stages=[]
        for R in [9,12,16,24,32,64,128,256]:
            f=objective(m,R);fits=[minimize(f,x,jac=True,bounds=[(.9609375,5)]*m,method='L-BFGS-B',
                 options={'ftol':2e-15,'gtol':2e-11,'maxiter':1000}) for x in seeds]
            best=min(fits,key=lambda z:z.fun);seeds.append(best.x)
            inf,parts=poisson(best.x)
            stages.append({'R':R,'gaps':best.x.tolist(),'finite_periodic_energy':float(best.fun),
                'infinite_periodic_energy_by_floating_Poisson':inf,
                'infinite_tail_after_R_at_same_gaps':inf-float(best.fun),
                'implied_percent_if_finite_energy_were_global_floor':100*(.6721684105641189-B)/(1-best.fun)})
        inf0,parts0=poisson(initial)
        row={'period':m,'old_R9_optimizer':initial,'old_optimizer_infinite_energy':inf0,
            'old_optimizer_Poisson_nonzero_modes':parts0,'stages':stages}
        rows.append(row);print(json.dumps(row),flush=True)
    out={'scope':__doc__,'parameter_sha256':hashlib.sha256(PAR.read_bytes()).hexdigest(),
         'fixed_pressure':B,'fixed_old_rank_totals':RANK9.tolist(),'new_rank_totals':2,
         'results':rows,'seconds':time.monotonic()-start,'arbitrary_chain_lower_bound_proven':False,
         'new_unconditional_zeta_bound_proven':False}
    (HERE/'global_tail_probe.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
if __name__=='__main__':main()
