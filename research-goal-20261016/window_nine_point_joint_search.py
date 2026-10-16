"""Joint profile/ledger exchange with nine points, preserving the full goal.

This is a numerical alternative for a smaller certificate dimension. The
Fourier profile itself is optimized subject to the proven generic l1 budget;
no sampled minimum or local adversary is presented as a global lower bound.
The ten-point proof and its frozen parameters are not modified.
"""
from pathlib import Path
import argparse,hashlib,json,time
import numpy as np
from scipy.optimize import minimize
import window_nine_point_search as base
wc=base.wc;profile=base.profile;HERE=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--rounds',type=int,default=16)
    ap.add_argument('--starts',type=int,default=160);ap.add_argument('--output',type=Path,default=HERE/'window-nine-point-joint-search.json');args=ap.parse_args()
    initial=json.loads((HERE/'window-nine-point-search.json').read_bytes())
    with np.load(HERE/'window-nine-point-search.npz') as old:samples=old['gaps'].copy()
    coeff=np.array(initial['fixed_window_coefficient_numerators_1e9'])/1e9
    n=9;model=wc.model(n);pairs,inc,am,bm,cap=model;rng=np.random.default_rng(20261016091)
    e=(.5-1/(4*np.pi**2*np.arange(1,25)**2))/profile.Z**2
    start=time.monotonic();history=[]
    for iteration in range(args.rounds):
        wc.H=float(profile.H(coeff));wc.base.kernel=lambda x:profile.bases(x,24)@np.r_[1,coeff];wc.DP_CACHE.clear()
        feats=np.concatenate([(profile.bases(chunk@inc.T,24)@np.r_[1,coeff])**2 for chunk in np.array_split(samples,max(1,len(samples)//1000))])
        a,b,cf,B,score=wc.solve(samples,feats,n,model)
        if iteration%2==0:
            # Exact analytic quadratic dependence on the Fourier coefficients.
            z=profile.bases(samples@inc.T,24);z0=z[:,:,0];zc=z[:,:,1:]
            mats=np.einsum('spi,p,spj->sij',zc,a,zc)
            linear=2*np.einsum('sp,p,spi->si',z0,a,zc)
            constant=np.einsum('sp,p,sp->s',z0,a,z0)+samples@b
            def values(c):return constant+linear@c+np.einsum('i,sij,j->s',c,mats,c)
            def fun(z):return -(profile.H(z[:-1])-B)/(1-z[-1])
            def jac(z):return np.r_[2*e*z[:-1]/(1-z[-1]),-(profile.H(z[:-1])-B)/(1-z[-1])**2]
            constraints=[{'type':'ineq','fun':lambda z:values(z[:-1])-z[-1],
                'jac':lambda z:np.c_[linear+2*np.einsum('sij,j->si',mats,z[:-1]),-np.ones(len(samples))]},
              {'type':'ineq','fun':lambda z:.0799995-np.sum(np.abs(z[:-1])),
                'jac':lambda z:np.r_[-np.sign(z[:-1]),0.]}]
            fit=minimize(fun,np.r_[coeff,min(values(coeff))],jac=jac,constraints=constraints,
                bounds=[(-.08,.08)]*24+[(.006,.012)],method='SLSQP',options={'ftol':1e-12,'maxiter':90})
            if fit.success and np.sum(np.abs(fit.x[:-1]))<=.07999951:coeff=fit.x[:-1]
            del z,zc,z0,mats,linear,constant
        wc.H=float(profile.H(coeff));wc.DP_CACHE.clear()
        def energy(g):
            x=inc@g;k=profile.bases(x,24)@np.r_[1,coeff];kp=profile.bases(x,24,True)@np.r_[1,coeff]
            return float(a@(k*k)+b@g),inc.T@(2*a*k*kp)+b
        energies=np.array([energy(g)[0] for g in samples]);order=np.argsort(energies)
        starts=list(samples[order[:args.starts]])
        starts+=list(rng.choice([1.04,1.97,2.915,3.9,4.9],(args.starts//2,8))+rng.normal(0,.025,(args.starts//2,8)))
        starts+=[wc.discrete_dp(n,a,b,pairs,alphabet,8) for alphabet in [(1.04,1.97,2.915),(1.02,1.95,2.9),(1.06,2.,2.94)]]
        upper=np.maximum(20,np.minimum(4096,.03/np.maximum(b,1e-14)))
        for pos in np.argsort(b)[:3]:
            for value in [12,64,1024]:
                g=np.full(8,1.04);g[pos]=value;starts.append(g)
        found=[]
        for g in starts:
            fit=minimize(energy,np.clip(g,.9609375,upper),jac=True,method='L-BFGS-B',bounds=list(zip(np.full(8,.9609375),upper)),
              options={'ftol':1e-14,'gtol':1e-9,'maxiter':500,'maxls':40})
            found.append((float(fit.fun),fit.x))
        found.sort(key=lambda r:r[0]);v,g=found[0];current_sample_min=float(min(energies))
        row={'iteration':iteration,'current_sample_minimum':current_sample_min,'observed_minimum_upper_hint':v,
             'observed_score_not_bound':(wc.H-B)/(1-v),'profile_H_hint':wc.H,'B':B,'profile_l1':float(np.sum(abs(coeff))),
             'violation':current_sample_min-v,'worst_gaps':g.tolist(),'sample_count':len(samples)}
        history.append(row)
        out={'scope':__doc__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'points':9,
             'window_coefficients_float':coeff.tolist(),'a':[[i,j,float(v)] for (i,j),v in zip(pairs,a)],'b':b.tolist(),
             'history':history,'global_floor_proven':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
        args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(row),flush=True)
        samples=np.r_[samples,np.array([g for v,g in found])]
    np.savez_compressed(args.output.with_suffix('.npz'),gaps=samples)
if __name__=='__main__':main()
