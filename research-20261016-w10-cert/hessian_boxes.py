"""Numerical whole-objective curvature probe on large certified subtrees.

Sampled scalar minima are exploratory and are NOT interval certificates.
"""
from pathlib import Path
import json,time
import numpy as np
import ordered_generate as o
g=o.g
FREQ=g.KFREQ;COEF=g.KCOEF
INC=np.array([[int(i<=r<j) for r in range(9)] for i,j,a in g.TERMS],float)
AW=np.array([a/g.D for i,j,a in g.TERMS])
def dsinc(z):
    z=np.asarray(z);out=np.empty_like(z);small=np.abs(z)<1e-3;v=z[small]
    out[small]=-np.pi**2*v/3+np.pi**4*v**3/30-np.pi**6*v**5/840
    v=z[~small];out[~small]=(np.pi*v*np.cos(np.pi*v)-np.sin(np.pi*v))/(np.pi*v*v)
    return out
def d2sinc(z):
    z=np.asarray(z);out=np.empty_like(z);small=np.abs(z)<1e-3;v=z[small]
    out[small]=-np.pi**2/3+np.pi**4*v*v/10-np.pi**6*v**4/168
    v=z[~small];out[~small]=-np.pi*np.sin(np.pi*v)/v-2*np.cos(np.pi*v)/(v*v)+2*np.sin(np.pi*v)/(np.pi*v**3)
    return out
def w2(t):
    t=np.asarray(t);u=t[:,None]+FREQ;v=t[:,None]-FREQ
    kv=(np.sinc(u)+np.sinc(v))@COEF/(2*g.KNORM)
    dv=(dsinc(u)+dsinc(v))@COEF/(2*g.KNORM)
    dd=(d2sinc(u)+d2sinc(v))@COEF/(2*g.KNORM)
    return 2*(dv*dv+kv*dd)
def norm(s):
    for _ in range(2):s=o.rawsplit(s,0,s[1][8],True);s=o.rawsplit(s,8,s[0][0],False)
    return s
def main():
    here=Path(__file__).parent;x=json.loads((here/'ordered-0.json').read_text());seed=json.loads((here/'ordered-seed-0.json').read_text())['unresolved'][0]
    nodes={z['path']:z for z in x['branches']};leaves={z['path']:z for z in x['accepted']}
    sizes={p:(0 if z['result'].get('empty') else 1) for p,z in leaves.items()}
    for p in sorted(nodes,key=len,reverse=True):sizes[p]=sizes.get(p+'0',0)+sizes.get(p+'1',0)
    todo=[(seed['path'],seed['state'])];candidates=[]
    while todo:
        p,s=todo.pop();s=norm(s)
        if p in nodes:
            n=sizes[p]
            if 20<=n<=1000:
                width=max((u-l)/g.SC for l,u in zip(s[0][:9],s[1][:9]));candidates.append((width,p,n,s))
            z=nodes[p]
            todo.append((p+'1',o.rawsplit(s,z['axis'],z['cut'],False)));todo.append((p+'0',o.rawsplit(s,z['axis'],z['cut'],True)))
    start=time.monotonic();out=[]
    # Probe both large macro cells and smaller nearly-convex cells.
    chosen=sorted([r for r in candidates if r[2]>=100])[:80]+sorted([r for r in candidates if r[2]<100])[:40]
    for width,p,n,s in chosen:
        lo,hi=s;curv=[]
        for i,j,a in g.TERMS:
            z=g.LOOK[i,j];grid=np.linspace(lo[z]/g.SC,hi[z]/g.SC,301);curv.append(float(min(w2(grid))))
        curv=np.array(curv);M=INC.T@(AW[:,None]*curv[:,None]*INC);eig=float(np.linalg.eigvalsh(M)[0])
        gersh=float(min(M[i,i]-sum(abs(M[i,j]) for j in range(9) if i!=j) for i in range(9)))
        out.append({'path':p,'old_numeric_leaves':n,'max_gap_width':width,'sampled_M_min_eigenvalue':eig,
            'negative_term_curvatures':int(sum(curv<0)),'gershgorin_lower':gersh,
            'lower_bounds':lo,'upper_bounds':hi,'sampled_curvature_minima':curv.tolist()})
    positive=[z for z in out if z['sampled_M_min_eigenvalue']>0]
    result={'scope':__doc__,'candidate_subtrees':len(candidates),'probed':len(out),'positive_sampled_M':len(positive),
        'largest_numeric_subtree_with_positive_sampled_M':max((z['old_numeric_leaves'] for z in positive),default=0),
        'seconds':time.monotonic()-start,'results':out}
    (here/'hessian-subtree-probe.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='results'}),flush=True)
    print(json.dumps(sorted(positive,key=lambda z:z['old_numeric_leaves'],reverse=True)[:3]),flush=True)
if __name__=='__main__':main()
