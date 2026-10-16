"""Change the Fourier window itself. Floating discovery, never a global floor.

All H values are from the exact analytic quadratic identity; floating
evaluation and sampled adversaries here are supporting research only.
"""
from __future__ import annotations
import argparse, itertools, json, time
from pathlib import Path
import numpy as np
from scipy.optimize import minimize

ROOT=Path(__file__).resolve().parents[1]
OLD=ROOT/'research-20261016'
BASE=np.array([12310798,-15041681,3867664,6489926,-992327,5580097,
              -6846472,3781297,-5670353,3355089,-450523,-218483])/1e9
ALPHA=np.sqrt(2)/(2*np.pi); Z=np.sinc(ALPHA)
H0=1.5-np.cos(np.sqrt(2)/2)/Z
REC=json.loads((OLD/'spectral-w10-refined-rational.json').read_text())
PAIRS=[(i,j) for i,j,v in REC['a_upper']]
A=np.array([v/1e10 for i,j,v in REC['a_upper']])
B=np.array(REC['b_numerators'])/1e10
INC=np.array([[i<=r<j for r in range(9)] for i,j in PAIRS],float)

def sincprime(x):
    x=np.asarray(x); small=abs(x)<1e-4; y=np.where(small,1,x)
    return np.where(small,-np.pi**2*x/3+np.pi**4*x**3/30,
       (np.pi*y*np.cos(np.pi*y)-np.sin(np.pi*y))/(np.pi*y*y))

def bases(x,m,prime=False):
    fn=sincprime if prime else np.sinc; x=np.asarray(x)
    f=np.r_[ALPHA,np.arange(1,m+1)]
    return (fn(x[...,None]+f)+fn(x[...,None]-f))/(2*Z)

def H(c):
    j=np.arange(1,len(c)+1);e=.5-1/(4*np.pi**2*j*j)
    return H0-np.dot(e,c*c)/Z**2

def objective(g,c,grad=False):
    x=INC@g; q=bases(x,len(c)); k=q@np.r_[1,c]
    v=float(np.dot(A,k*k)+np.dot(B,g))
    if not grad:return v
    kp=bases(x,len(c),True)@np.r_[1,c]
    return v,INC.T@(2*A*k*kp)+B

def compress(gaps,limit=800):
    rounded=np.round(gaps,5)
    _,idx=np.unique(rounded,axis=0,return_index=True)
    gaps=gaps[np.sort(idx)]
    if len(gaps)>limit:
        score=np.array([objective(g,BASE) for g in gaps])
        gaps=gaps[np.argsort(score)[:limit]]
    return gaps

def optimize_window(samples,c):
    m=len(c); q=bases(samples@INC.T,m)
    q0=q[:,:,0];qc=q[:,:,1:]
    mats=np.einsum('spi,p,spj->sij',qc,A,qc)
    linear=2*np.einsum('sp,p,spi->si',q0,A,qc)
    constant=np.einsum('sp,p,sp->s',q0,A,q0)+samples@B
    e=(.5-1/(4*np.pi**2*np.arange(1,m+1)**2))/Z**2
    def vals(cc):return constant+linear@cc+np.einsum('i,sij,j->s',cc,mats,cc)
    def fun(z):
        cc=z[:-1];floor=z[-1];hh=H0-np.dot(e,cc*cc)
        return -(hh-B.sum())/(1-floor)
    def jac(z):
        cc=z[:-1];f=z[-1];hh=H0-np.dot(e,cc*cc)
        return np.r_[2*e*cc/(1-f),-(hh-B.sum())/(1-f)**2]
    def con(z):return vals(z[:-1])-z[-1]
    def conjac(z):return np.c_[linear+2*np.einsum('sij,j->si',mats,z[:-1]),-np.ones(len(samples))]
    fit=minimize(fun,np.r_[c,min(vals(c))],jac=jac,method='SLSQP',
        constraints=[{'type':'ineq','fun':con,'jac':conjac}],
        bounds=[(-.1,.1)]*m+[(.005,.03)],
        options={'maxiter':120,'ftol':1e-13,'disp':False})
    return fit,vals(fit.x[:-1])

def main():
    p=argparse.ArgumentParser();p.add_argument('--modes',type=int,default=12)
    p.add_argument('--rounds',type=int,default=12);p.add_argument('--starts',type=int,default=100)
    p.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=p.parse_args();start=time.monotonic();rng=np.random.default_rng(161016)
    known=np.load(OLD/'spectral-wcert-reopt-full-ternary-samples-n10.npz')['gaps']
    known=np.maximum(.85,known)
    samples=compress(known)
    samples=np.r_[samples,np.array(list(itertools.product([1.04,1.97],repeat=9))),
      np.full((1,9),.85),rng.uniform(.85,4,(100,9))]
    c=np.pad(BASE,(0,args.modes-len(BASE)))
    baseline=min(objective(g,c) for g in samples)
    report={'status':'FLOATING_RESEARCH_ONLY_NO_GLOBAL_FLOOR',
      'window_family':'cos(sqrt(2)t)+sum_j c_j cos(2 pi j t), normalized integral',
      'fixed_weight_source':'research-20261016/spectral-w10-refined-rational.json',
      'new_lean_proof':False,'baseline_sample_floor':baseline,'baseline_H':H(c),
      'baseline_sample_percent':100*(H(c)-B.sum())/(1-baseline),'history':[]}
    for it in range(args.rounds):
        fit,sv=optimize_window(samples,c);c=fit.x[:-1]
        ranked=np.argsort(sv)[:args.starts]
        starts=list(samples[ranked]);starts+=list(rng.choice([1.04,1.97,2.915,3.9],(args.starts//2,9)))
        starts+=list(rng.uniform(.85,4,(args.starts//5,9)))
        found=[]
        for g in starts:
            f=minimize(lambda x:objective(x,c,True),g,jac=True,method='L-BFGS-B',
                bounds=[(.85,40)]*9,options={'gtol':1e-10,'ftol':1e-15,'maxiter':300})
            found.append((float(f.fun),f.x.copy()))
        found.sort(key=lambda z:z[0]);worst,g=found[0]
        hh=H(c);row={'iteration':it,'optimizer_success':bool(fit.success),
            'coefficients':c.tolist(),'H':hh,'sample_floor':float(fit.x[-1]),
            'observed_minimum_upper':worst,'adversarial_gaps':g.tolist(),
            'observed_percent_not_bound':100*(hh-B.sum())/(1-worst),
            'sample_percent_upper_for_window':100*(hh-B.sum())/(1-fit.x[-1]),
            'sample_count':len(samples),'sample_constraint_violation':float(fit.x[-1]-worst)}
        report['history'].append(row);report['elapsed_seconds']=time.monotonic()-start
        args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf8')
        print(it,row['observed_percent_not_bound'],row['sample_constraint_violation'],hh,flush=True)
        samples=np.r_[samples,np.array([g for _,g in found])]
        if it>4 and abs(fit.x[-1]-worst)<1e-10:break
    report['final_window_coefficient_numerators_1e9']=[int(round(x*1e9)) for x in c]
    report['minimum_sampled_profile_value']=float(np.min(np.cos(np.sqrt(2)*np.linspace(-.5,.5,2001))+
        np.cos(2*np.pi*np.linspace(-.5,.5,2001)[:,None]*np.arange(1,len(c)+1))@c))
    args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf8')
    np.savez_compressed(args.output.with_suffix('.npz'),gaps=samples,coefficients=c)

if __name__=='__main__':main()
