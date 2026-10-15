"""Continuously polish every one of3^9 ternary W10 seeds, without symmetry reduction."""
from pathlib import Path
import importlib.util,itertools,json,time,hashlib,argparse
import numpy as np
from scipy.optimize import minimize
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('wcert',HERE/'spectral_wcert_reopt.py')
w=importlib.util.module_from_spec(spec);spec.loader.exec_module(w)
parser=argparse.ArgumentParser();parser.add_argument('--candidate',type=Path,default=HERE/'spectral-w10-rational.json')
parser.add_argument('--output-prefix',default='spectral-w10-full-ternary');args=parser.parse_args()
source=args.candidate;doc=json.loads(source.read_text());n=10
pairs,incidence,*_=w.model(n);D=doc['denominator']
a=np.array([r[2]/D for r in doc['a_upper']]);b=np.array(doc['b_numerators'])/D
alphabet=(1.04,1.97,2.915);patterns=list(itertools.product(alphabet,repeat=n-1))
upper=.025/b;started=time.monotonic();gaps=[];values=[];success=[];gradients=[]
def fun(g):
    value,derivative=w.fast_w(incidence@g)
    return float(np.dot(a,value)+np.dot(b,g)),incidence.T@(a*derivative)+b
progress=HERE/(args.output_prefix+'-progress.json')
for index,pattern in enumerate(patterns):
    fit=minimize(fun,np.asarray(pattern),jac=True,bounds=list(zip(np.full(n-1,.8),upper)),
        method='L-BFGS-B',options={'ftol':1e-14,'gtol':1e-9,'maxiter':500,'maxls':40})
    gaps.append(fit.x);values.append(float(fit.fun));success.append(bool(fit.success));gradients.append(float(np.max(np.abs(fit.jac))))
    if index%1000==0 or index+1==len(patterns):
        best=int(np.argmin(values));record={'scope':'Numerical full ternary basin sampling; no global proof',
            'candidate_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'alphabet':alphabet,'completed_patterns':index+1,'total_patterns':len(patterns),
            'best_observed_c_upper_bound':values[best],'best_gaps':gaps[best].tolist(),
            'elapsed_seconds':time.monotonic()-started,'status':'running' if index+1<len(patterns) else 'complete'}
        progress.write_text(json.dumps(record,indent=2)+'\n')
        print(index+1,values[best],record['elapsed_seconds'],flush=True)
np.savez_compressed(HERE/(args.output_prefix+'.npz'),gaps=np.asarray(gaps),values=np.asarray(values),
    success=np.asarray(success),gradient_inf=np.asarray(gradients),alphabet=np.asarray(alphabet))
record.update(successful_optimizations=sum(success),maximum_gradient_inf=max(gradients),
    gradient_inf_quantiles=np.quantile(gradients,[.5,.9,.99,1]).tolist(),
    minimum_grid_start_count=len(patterns),sample_data=args.output_prefix+'.npz')
(HERE/(args.output_prefix+'.json')).write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
