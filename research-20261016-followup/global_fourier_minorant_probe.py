"""Research-only Gaussian-Hermite positive-Fourier minorant LP.

Uses h(t)=sum_j c_j H_{2j}(sqrt(pi*a)*t)/H_{2j}(0)*exp(-pi*a*t^2),
c_j >= 0. Every basis Fourier transform is nonnegative and only j=0
contributes at frequency zero. Tail nonpositivity is imposed by all
translated polynomial coefficients <=0 for t^2 >= T^2. Finite sampled
constraints h<=w are NOT a proof between grid points.
"""
from pathlib import Path
import hashlib,json,sys,time,math
import numpy as np
from scipy.optimize import linprog,brentq
from scipy.special import eval_hermite
from numpy.polynomial import Polynomial
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
sys.path.insert(0,str(ROOT/'research-20261016-w10-unconditional'))
import analytic_memory_probe as k
PAR=ROOT/'research-20261016/spectral-w10-refined-rational.json';DOC=json.loads(PAR.read_text());B=sum(DOC['b_numerators'])/DOC['denominator']
def coeff_u(j,a):
    # H_2j(sqrt(pi*a)*t)/H_2j(0) as polynomial in u=t^2.
    return np.array([(-1)**l*math.factorial(j)*4**l*(np.pi*a)**l/
        (math.factorial(j-l)*math.factorial(2*l)) for l in range(j+1)])
def matrix(grid,a,K):
    z=np.sqrt(np.pi*a)*grid;gauss=np.exp(-z*z)
    return np.array([eval_hermite(2*j,z)/eval_hermite(2*j,0)*gauss for j in range(K+1)]).T
def main():
    start=time.monotonic();rows=[];best=None;sep=123/128
    for K in [15,25]:
      for a in [.01,.02,.04,.08,.16]:
        T=float(np.sqrt((4*K+2)/(np.pi*a)))
        grid=np.linspace(sep,T,max(5000,int(T*100)))
        # Include every discovered exact-amplitude zero, not just uniform samples.
        amp,_=k.amplitude(grid);ix=np.where(amp[:-1]*amp[1:]<0)[0]
        zeros=[brentq(lambda t:k.amplitude(np.array([t]))[0][0],grid[i],grid[i+1],xtol=1e-14) for i in ix]
        grid=np.sort(np.r_[grid,zeros]);A=matrix(grid,a,K);w=k.amplitude(grid)[0]**2
        # Polynomial in s=u-T^2. All coefficients nonpositive imply h<=0 beyond T.
        tail=np.zeros((K+1,K+1))
        for j in range(K+1):
            c=coeff_u(j,a)
            for l in range(j+1):
                tail[l,j]=sum(c[m]*math.comb(m,l)*T**(2*(m-l)) for m in range(l,j+1))
        scale=np.max(abs(tail),axis=1);tail=tail/scale[:,None]
        AA=np.r_[A,tail];bb=np.r_[w,np.zeros(K+1)]
        successes=0;localbest=None
        for c0 in np.geomspace(1e-5,.25,26):
            eq=np.zeros((1,K+1));eq[0,0]=1
            fit=linprog(np.ones(K+1),A_ub=AA,b_ub=bb,A_eq=eq,b_eq=[c0],bounds=[(0,None)]*(K+1),method='highs')
            if not fit.success:continue
            successes+=1;hat0=c0/np.sqrt(a);h0=fit.x.sum();floor=2*np.sqrt(B*hat0)-h0
            if localbest is None or floor>localbest['sampled_density_floor']:
                checkgrid=np.linspace(sep,T,30001);viol=matrix(checkgrid,a,K)@fit.x-k.amplitude(checkgrid)[0]**2
                localbest={'sampled_density_floor':float(floor),'h0':float(h0),'hat0':float(hat0),
                  'coefficients':fit.x.tolist(),'max_refined_grid_minorant_violation':float(max(viol)),
                  'max_coarse_constraint_violation':float(max(AA@fit.x-bb)),
                  'ratio_if_floor_were_proven':float(100*(.6721684105641189-B)/(1-floor))}
        row={'K':K,'a':a,'tail_from_T':T,'grid_points':len(grid),'kernel_zeros_included':len(zeros),
             'feasible_amplitudes':successes,'best':localbest};rows.append(row);print(json.dumps(row),flush=True)
        if localbest and (best is None or localbest['sampled_density_floor']>best['best']['sampled_density_floor']):best=row
    out={'scope':__doc__,'parameter_sha256':hashlib.sha256(PAR.read_bytes()).hexdigest(),
         'results':rows,'best':best,'seconds':time.monotonic()-start,
         'minorant_verified_globally':False,'density_bound_formalized':False,'new_unconditional_zeta_bound_proven':False}
    (HERE/'global_fourier_minorant_probe.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
if __name__=='__main__':main()
