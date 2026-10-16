"""Check actual kernel values at difficult LP points and local descendants.

These are numerical diagnostics, never certificates of a global lower bound.
"""
from pathlib import Path
import hashlib, importlib.util, json, time
import mpmath as mp
import numpy as np
from scipy.optimize import minimize
import ordered_generate as o
g=o.g
spec=importlib.util.spec_from_file_location('overlap_kernel',g.ROOT/'research-20261016/overlap_average.py')
k=importlib.util.module_from_spec(spec);spec.loader.exec_module(k)
mp.mp.dps=80
CF=[mp.mpf(1)]+[mp.mpf(x)/10**9 for x in [12310798,-15041681,3867664,6489926,-992327,5580097,-6846472,3781297,-5670353,3355089,-450523,-218483]]
FQ=[mp.sqrt(2)/(2*mp.pi)]+list(map(mp.mpf,range(1,13)))
def sinc(x):return mp.mpf(1) if x==0 else mp.sin(mp.pi*x)/(mp.pi*x)
NORM=sum(c*sinc(a) for c,a in zip(CF,FQ))
INC=np.array([[int(i<=r<j) for r in range(9)] for i,j,a in g.TERMS],dtype=float)
AW=np.array([a/g.D for i,j,a in g.TERMS]);BW=np.array(g.BS)/g.D
def fun(v):
    w,dw=k.kernel(INC@v)
    return float(AW@w+BW@v),BW+INC.T@(AW*dw)
def high(v):
    vv=[mp.mpf(str(x)) for x in v];out=sum(mp.mpf(b)*x/g.D for b,x in zip(g.BS,vv))
    for i,j,a in g.TERMS:
        s=sum(vv[i:j]);kv=sum(c*(sinc(s-f)+sinc(s+f))/2 for c,f in zip(CF,FQ))/NORM
        out+=mp.mpf(a)*kv**2/g.D
    return str(out)
def main():
    here=Path(__file__).parent;names=['ordered-1-0.json','ordered-1-1.json'];records=[];inputs=[];started=time.monotonic()
    for name in names:
        raw=(here/name).read_bytes();doc=json.loads(raw);inputs.append({'path':name,'sha256':hashlib.sha256(raw).hexdigest()})
        rows=sorted(doc['unresolved'],key=lambda r:r['depth'],reverse=True)
        for row in rows:
            state,cuts=o.normalize(row['state'])
            if any(l>u for l,u in zip(*state)):continue
            rec=g.certify(state,False)
            if 'gaps' not in rec:continue
            v=np.array(rec['gaps']);vf=fun(v)[0]
            fit=minimize(fun,v,jac=True,method='L-BFGS-B',bounds=[(.85,u/g.SC) for u in g.root()[1][:9]],
                options={'ftol':1e-15,'gtol':1e-11,'maxiter':1000,'maxls':50})
            records.append({'source':name,'path':row['path'],'depth':row['depth'],'lp_floor':rec['lp_floor'],
                'lp_point_actual_Fw':vf,'lp_point_actual_Fw_80_digits':high(v),'lp_gaps':v.tolist(),
                'local_minimum':float(fit.fun),'local_minimum_80_digits':high(fit.x),'local_gaps':fit.x.tolist(),
                'optimizer_success':bool(fit.success)})
    best=min(records,key=lambda r:r['local_minimum'])
    out={'scope':__doc__,'inputs':inputs,'separation_lower':.85,'parameter_sha256':hashlib.sha256(g.PAR.read_bytes()).hexdigest(),
        'checked_frontier_points':len(records),'minimum_actual_at_lp_points':min(r['lp_point_actual_Fw'] for r in records),
        'best_local_minimum':best['local_minimum'],'best_local_minimum_80_digits':best['local_minimum_80_digits'],
        'best_margin_to_target':best['local_minimum']-.00866,'best_gaps':best['local_gaps'],'results':records,
        'seconds':time.monotonic()-started}
    (here/'frontier-actual-diagnostic.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({a:b for a,b in out.items() if a not in ['results','scope','inputs']},indent=2),flush=True)
if __name__=='__main__':main()
