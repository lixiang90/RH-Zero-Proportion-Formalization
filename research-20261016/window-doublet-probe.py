"""Floating-point obstruction to fixed-weight window doublets, not a proof.
The seed is a low-margin certificate leaf. Its local minimizer supplies one
explicit necessary test for uniform improvement, not a global minimum claim.
"""
from pathlib import Path
import sys,json,time,hashlib
import numpy as np
from scipy.optimize import minimize
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import finite_margin_20261015 as data
COEFF=np.array([12310798,-15041681,3867664,6489926,-992327,5580097,-6846472,3781297,-5670353,3355089,-450523,-218483])/1e9
Z=np.sqrt(2)*np.sin(np.sqrt(2)/2)
H0=0.6721684105641188747759983512104999330646
KAPPA=3338957652820594373879991756052499665323/4957023073704306225950000000000000000000
BS=np.array(data.BS,dtype=float)/1e20
A=np.array([term[2] for term in data.TS],dtype=float)/1e20
INC=np.array([[float(i<=r<j) for r in range(8)] for i,j,_,_ in data.TS])
B=float(BS.sum())
def dsinc(x):
 x=np.asarray(x);small=np.abs(x)<1e-5;safe=np.where(small,1.,x)
 regular=(np.pi*safe*np.cos(np.pi*safe)-np.sin(np.pi*safe))/(np.pi*safe**2)
 return np.where(small,-np.pi**2*x/3+np.pi**4*x**3/30,regular)
def basis(x,n=12,derivative=False):
 f=dsinc if derivative else np.sinc;x=np.asarray(x)[...,None];j=np.arange(1,n+1)
 return (f(x-j)+f(x+j))/2
def kernel(x,derivative=False):
 f=dsinc if derivative else np.sinc;a=np.sqrt(2)/(2*np.pi);x=np.asarray(x)
 return ((f(x-a)+f(x+a))/2+basis(x,12,derivative)@COEFF)/Z
def objective(g):
 d=INC@g;k=kernel(d);kd=kernel(d,True)
 return float(BS@g+A@(k*k)),BS+(A*(2*k*kd))@INC
def main():
 start=time.time();seed=np.array([33955,64226,33958,33771,64335,34144,64520,34000])/32768
 result=minimize(objective,seed,jac=True,bounds=[(.01,32)]*8,method='L-BFGS-B',options={'ftol':1e-15,'gtol':1e-12,'maxiter':1000})
 assert result.success
 d=INC@result.x;spectra=[]
 for n in [8,12,16,24,32,48,64,96,128,192,256,512,1024]:
  j=np.arange(1,n+1);q=.5-1/(4*np.pi**2*j*j);t=np.sqrt(A)[:,None]*basis(d,n)/np.sqrt(q)
  largest=float(np.linalg.eigvalsh(t@t.T)[-1]);tail=None
  if n>max(d):
   tail=float((A@(d*d))/(np.pi**2*(1-max(d)**2/(n+1)**2)**2*(.5-1/(4*np.pi**2*(n+1)**2))*3*n**3))
  spectra.append({'basis_terms':n,'lambda_max':largest,'kappa_lambda_minus_one':KAPPA*largest-1,'coarse_infinite_tail_trace_bound':tail})
 report={'scope':'Floating-point research only; no rigorous global or Lean certificate','model':'Equal-integral v0+epsilon*g and v0-epsilon*g, same pair weights','quadratic_identity':'h_eff=h0-epsilon^2*Q(g)/Z^2; c_eff=c0+epsilon^2*E(g)/Z^2','basis':'g=sum a_j*cos(2*pi*j*s); Q(g)=sum (1/2-1/(4*pi^2*j^2))*a_j^2','directional_test':'Positive improvement requires E(g)/Q(g)>1/kappa','published_kappa':KAPPA,'necessary_eigenvalue_threshold':1/KAPPA,'seed_from_certificate_leaf':seed.tolist(),'seed_objective':objective(seed)[0],'configuration':result.x.tolist(),'configuration_objective':float(result.fun),'configuration_gradient_max':float(max(abs(objective(result.x)[1]))),'baseline_upper_score_at_this_configuration':float((H0-B)/(1-result.fun)),'spectra':spectra,'conclusion':'No tested same-support fixed-weight variance direction improves the score; PSD mixtures cannot exceed the largest Rayleigh quotient at this configuration.','finite_source_sha256':hashlib.sha256(data.SRC.read_bytes()).hexdigest(),'seconds':time.time()-start}
 Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps(report,indent=2))
if __name__=='__main__':main()
