"""Test a global minimizer localization by dominant adjacent potentials.

At an interior coordinate minimum the total gradient vanishes, and its
diagonal Hessian is nonnegative. Nonadjacent spans containing that coordinate
have length at least g+(rank-1)*sep; tail envelopes bound their possible
gradient/curvature payments. This floating diagnostic is NOT a rigorous
envelope, a Lean localization theorem, or a zero-proportion result.
"""
from pathlib import Path
import hashlib,json,time
import numpy as np
HERE=Path(__file__).parent;ROOT=HERE.parent
PARAM=ROOT/'research-20261016-followup/window_reweight_rational.json'

def curves(x,coeff):
    f=np.r_[np.sqrt(2)/(2*np.pi),np.arange(1,25)]
    def sinc1(z):
        small=abs(z)<.002;y=np.where(small,1,z);u=np.pi*y
        return np.where(small,-np.pi**2*z/3+np.pi**4*z**3/30-np.pi**6*z**5/840,
          (u*np.cos(u)-np.sin(u))/(np.pi*y*y))
    def sinc2(z):
        small=abs(z)<.002;y=np.where(small,1,z);u=np.pi*y
        return np.where(small,-np.pi**2/3+np.pi**4*z*z/10-np.pi**6*z**4/168,
          ((2-u*u)*np.sin(u)-2*u*np.cos(u))/(np.pi*y*y*y))
    z=np.sinc(f[0]);out=[]
    for chunk in np.array_split(x,max(1,len(x)//4096)):
        p=chunk[:,None]+f;m=chunk[:,None]-f
        k=(np.sinc(p)+np.sinc(m))@coeff/(2*z)
        d=(sinc1(p)+sinc1(m))@coeff/(2*z)
        dd=(sinc2(p)+sinc2(m))@coeff/(2*z)
        out.append(np.c_[k*k,2*k*d,2*d*d+2*k*dd])
    return np.concatenate(out)

def runs(mask,x):
    ix=np.flatnonzero(mask)
    if not len(ix):return []
    starts=np.r_[ix[0],ix[1:][np.diff(ix)>1]];ends=np.r_[ix[:-1][np.diff(ix)>1],ix[-1]]
    return [[float(x[l]),float(x[r])] for l,r in zip(starts,ends)]

def main():
    start=time.monotonic();p=json.loads(PARAM.read_bytes());coeff=np.r_[1,np.array(p['window_coefficient_numerators_1e9'])/1e9]
    b=np.array(p['b_numerators'])/1e10;a={(i,j):v/1e10 for i,j,v in p['a_upper'] if v}
    step=1024;grid=np.arange(128*step+1)/step;data=curves(grid,coeff)
    max1=np.maximum.accumulate(abs(data[::-1,1]))[::-1]
    max2=np.maximum.accumulate(np.maximum(0,data[::-1,2]))[::-1]
    sep=123/128;c=.00884;up=sep+(c-sep*b.sum())/b
    result=[]
    for r in range(9):
        x=grid[(grid>=sep)&(grid<=up[r])];ix=np.round(x*step).astype(int)
        C1=np.zeros(len(x));C2=np.zeros(len(x))
        for (i,j),v in a.items():
            if i<=r<j and j>i+1:
                index=np.floor((x+(j-i-1)*sep)*step).astype(int)
                C1+=v*max1[index];C2+=v*max2[index]
        adj=a[r,r+1];gradient=b[r]+adj*data[ix,1]
        allowed1=abs(gradient)<=C1+1e-12
        allowed2=adj*data[ix,2]+C2>=-1e-12
        allowed=allowed1&allowed2;allowed[0]=True
        outside=abs(x-np.round(x))>.21
        result.append({'coordinate':r,'adjacent_weight':float(adj),'pressure_root_upper':float(up[r]),
          'gradient_allowed_intervals':runs(allowed1,x),'joint_allowed_intervals':runs(allowed,x),
          'outside_integer_cores_intervals':runs(allowed&outside,x),
          'joint_allowed_samples':int(allowed.sum()),'outside_core_samples':int((allowed&outside).sum())})
    out={'scope':__doc__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'parameter_sha256':hashlib.sha256(PARAM.read_bytes()).hexdigest(),'grid_step':f'1/{step}',
      'sampled_tail_endpoint':128,'curves_are_floating':True,'tail_envelopes_are_not_rigorous':True,
      'rows':result,'every_sampled_allowed_coordinate_inside_core':all(r['outside_core_samples']==0 for r in result),
      'global_localization_proven':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'seconds':out['seconds'],'all_inside':out['every_sampled_allowed_coordinate_inside_core'],
      'rows':[{k:r[k] for k in ['coordinate','joint_allowed_samples','outside_core_samples','outside_integer_cores_intervals']} for r in result]}))
if __name__=='__main__':main()
