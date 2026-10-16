"""Floating stationary-well diagnosis for patterns appearing in the frontier.

These optimization results are upper-bound hints, not certified floors.
"""
from pathlib import Path
import hashlib,json,time
import numpy as np
from scipy.optimize import minimize
import cover_newwindow_gram as gram
HERE=Path(__file__).parent;g=gram.g

def main():
    start=time.monotonic();raw=(HERE/'cover-current-frontier-20261017b.json').read_bytes();doc=json.loads(raw)
    patterns={tuple((r['state'][0][k]+r['state'][1][k]+g.SC)//(2*g.SC) for k in range(9)) for r in doc['frontier'] if r['depth']>=18}
    terms=g.TERMS;S=np.zeros((len(terms),9))
    for t,(i,j,aw) in enumerate(terms):S[t,i:j]=1
    weights=np.array([aw/g.D for i,j,aw in terms]);bs=np.array(g.BS)/g.D
    def value(x):return float(bs@x+weights@gram.w_value_derivative(S@x)[0])
    def grad(x):return bs+S.T@(weights*gram.w_value_derivative(S@x)[1])
    rows=[]
    for n0 in sorted(patterns):
        n=np.array(n0,dtype=float);trials=[]
        for offset in [-.04,0.,.04]:
            fit=minimize(value,np.maximum(123/128,n+offset),jac=grad,bounds=[(max(123/128,v-.3),v+.3) for v in n],
              method='L-BFGS-B',options={'ftol':1e-15,'gtol':1e-11,'maxiter':1000});trials.append(fit)
        best=min(trials,key=lambda r:r.fun);q=best.x;span_offsets=[float(sum(q[i:j])-sum(n[i:j])) for i,j,aw in terms]
        contained=[]
        for r in doc['frontier']:
            lo,hi=r['state']
            if all(lo[z]/g.SC<=sum(q[i:j])<=hi[z]/g.SC for z,(i,j) in enumerate(gram.g.ALL)):contained.append(r['path'])
        rows.append({'integer_pattern':list(n0),'anchor_hint':list(map(float,q)),'energy_hint':float(best.fun),'gradient_infinity_hint':float(max(abs(grad(q)))),
          'maximum_abs_positive_weight_span_offset':max(map(abs,span_offsets)),
          'positive_weight_spans_outside_integer_core':sum(abs(v)>.21 for v in span_offsets),'frontier_cells_containing_anchor_hint':contained,
          'optimization_success':bool(best.success)})
    out={'scope':__doc__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'snapshot_sha256':hashlib.sha256(raw).hexdigest(),
      'results':rows,'new_rigorous_exclusions':0,'global_floor_proven':False,'complete_global_cover':False,'seconds':time.monotonic()-start}
    (HERE/'cover-frontier-well-diagnostic.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
