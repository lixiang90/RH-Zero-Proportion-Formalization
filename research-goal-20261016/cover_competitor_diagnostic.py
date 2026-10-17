"""Locate the early integer wells and compare cross-well move geometries.

All optimization values here are floating diagnostics, never lower bounds.
"""
from pathlib import Path
import hashlib,json,time
import numpy as np
from scipy.optimize import minimize
import cover_newwindow_gram as gram
g=gram.g;HERE=Path(__file__).parent

def main():
    start=time.monotonic();terms=g.TERMS;S=np.zeros((len(terms),9))
    for t,(i,j,a) in enumerate(terms):S[t,i:j]=1
    aw=np.array([a/g.D for i,j,a in terms]);bs=np.array(g.BS)/g.D
    def value(x):return float(bs@x+aw@gram.w_value_derivative(S@x)[0])
    def grad(x):return bs+S.T@(aw*gram.w_value_derivative(S@x)[1])
    library=json.loads((HERE/'cover-newwindow-gram.json').read_bytes())['results'];targets=[r['integer_gaps'] for r in library]
    patterns=[[1]*9]+[[1+int(i==k) for i in range(9)] for k in range(9)];rows=[]
    for n in patterns:
        result=minimize(value,np.array(n,dtype=float)+.02,jac=grad,bounds=[(max(123/128,v-.25),v+.25) for v in n],method='L-BFGS-B',options={'ftol':1e-15,'gtol':1e-11,'maxiter':1000})
        q=result.x;direct=[];reflected=[]
        for p in targets:
            x=q+np.array(p)-np.array(n)
            if min(x)>=123/128:direct.append((value(x)-value(q),p))
            signs=np.array([1 if (a-b)%2==0 else -1 for a,b in zip(p,n)])
            x=np.array(p)+signs*(q-n)
            if min(x)>=123/128:reflected.append((value(x)-value(q),p))
        rows.append({'integer_pattern':n,'anchor_hint':list(map(float,q)),'F_hint':value(q),
          'gradient_infinity_hint':max(abs(grad(q))),'best_integer_translation_hint':min(direct) if direct else None,
          'best_parity_reflection_hint':min(reflected) if reflected else None})
    out={'scope':__doc__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'results':rows,
      'all_values_are_upper_bound_hints_only':True,'mathematical_exclusions_proven':0,'complete_global_cover':False,'seconds':time.monotonic()-start}
    (HERE/'cover-competitor-diagnostic.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
