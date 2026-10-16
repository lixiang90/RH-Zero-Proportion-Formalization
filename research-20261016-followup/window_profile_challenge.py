"""Adversarial exploration of a changed window. Never a lower certificate."""
from __future__ import annotations
import argparse, hashlib, importlib.util, itertools, json, time
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('win',HERE/'window_profile_search.py')
w=importlib.util.module_from_spec(spec);spec.loader.exec_module(w)

def main():
    p=argparse.ArgumentParser();p.add_argument('--source',type=Path,default=HERE/'window_profile_search.json')
    p.add_argument('--output',type=Path,default=HERE/'window_profile_challenge.json')
    p.add_argument('--ledger',type=Path,help='Optional frozen redesigned pair/pressure ledger')
    p.add_argument('--ternary',action='store_true');p.add_argument('--random',type=int,default=500)
    p.add_argument('--separation',type=float,default=.85);args=p.parse_args()
    doc=json.loads(args.source.read_text());nums=doc['final_window_coefficient_numerators_1e9']
    c=np.array(nums)/1e9;rng=np.random.default_rng(20261016);started=time.monotonic()
    if args.ledger:
        ledger=json.loads(args.ledger.read_text());den=ledger['denominator']
        assert [(i,j) for i,j,v in ledger['a_upper']]==w.PAIRS
        w.A=np.array([v/den for i,j,v in ledger['a_upper']]);w.B=np.array(ledger['b_numerators'])/den
    patterns=list(itertools.product([1.04,1.97,2.915],repeat=9)) if args.ternary else []
    for _ in range(args.random):
        typ=rng.integers(4)
        if typ==0:g=rng.uniform(args.separation,6,9)
        elif typ==1:g=rng.choice([.97,1.04,1.97,2.915,3.9,4.9],9)+rng.uniform(-.02,.02,9)
        elif typ==2:
            g=np.full(9,rng.uniform(.97,1.08));g[rng.choice(9,rng.integers(1,5),False)]=rng.uniform(2,40)
        else:g=rng.uniform(args.separation,2,9)
        patterns.append(np.clip(g,args.separation,40))
    findings=[];success=0;gradient=[]
    for index,pat in enumerate(patterns):
        fit=minimize(lambda g:w.objective(g,c,True),np.asarray(pat),jac=True,
            method='L-BFGS-B',bounds=[(args.separation,40)]*9,
            options={'gtol':1e-9,'ftol':1e-14,'maxiter':500,'maxls':40})
        findings.append((float(fit.fun),fit.x.tolist()));success+=bool(fit.success)
        gradient.append(float(np.max(abs(fit.jac))))
        if index%1000==0 or index+1==len(patterns):
            findings.sort(key=lambda z:z[0]);v,g=findings[0]
            record={'status':'RUNNING_FLOATING_CHALLENGE' if index+1<len(patterns) else 'COMPLETE_FLOATING_CHALLENGE',
              'scope':'Each local value is an upper bound on the true global minimum; no certified lower bound',
              'source_sha256':hashlib.sha256(args.source.read_bytes()).hexdigest(),
              'ledger_sha256':hashlib.sha256(args.ledger.read_bytes()).hexdigest() if args.ledger else None,
              'coefficient_numerators_1e9':nums,'completed_starts':index+1,'total_starts':len(patterns),
              'ternary_patterns':19683 if args.ternary else 0,'extra_random':args.random,
              'separation':args.separation,'best_observed_minimum_upper':v,'best_gaps':g,
              'H_float_not_lower_bound':w.H(c),'percent_from_observed_minimum_not_bound':100*(w.H(c)-w.B.sum())/(1-v),
              'successful_optimizations':success,'gradient_inf_quantiles':np.quantile(gradient,[.5,.9,.99,1]).tolist(),
              'elapsed_seconds':time.monotonic()-started,'best_30_findings':findings[:30]}
            args.output.write_text(json.dumps(record,indent=2)+'\n',encoding='utf8')
            print(index+1,v,record['elapsed_seconds'],flush=True)

if __name__=='__main__':main()
