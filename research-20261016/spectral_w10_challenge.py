"""Strong numerical adversaries against the fixed rational W10 candidate."""
from pathlib import Path
import importlib.util,itertools,json,time,argparse
import numpy as np
from scipy.optimize import minimize,differential_evolution
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('wcert',HERE/'spectral_wcert_reopt.py')
w=importlib.util.module_from_spec(spec);spec.loader.exec_module(w)
parser=argparse.ArgumentParser();parser.add_argument('--candidate',type=Path,default=HERE/'spectral-w10-rational.json')
parser.add_argument('--output-prefix',default='spectral-w10-challenge');args=parser.parse_args()
doc=json.loads(args.candidate.read_text());n=10
pairs,incidence,*_=w.model(n);D=doc['denominator']
a=np.array([r[2]/D for r in doc['a_upper']]);b=np.array(doc['b_numerators'])/D
c=433/50000;sep=.8;rng=np.random.default_rng(21161016);started=time.monotonic()
def fun(g):
    value,derivative=w.fast_w(incidence@g)
    return float(np.dot(a,value)+np.dot(b,g)),incidence.T@(a*derivative)+b
samples=np.array(list(itertools.product([1.04,1.98,2.92],repeat=n-1)))
values=w.feature(samples,incidence)@a+samples@b
top=np.argsort(values)[:256]
starts=[samples[i] for i in top]
for alphabet in [(1.04,1.98,2.92),(1.02,1.96,2.91),(1.06,2.,2.94),
                 (1.04,1.98,2.92,3.9),(1.03,1.96,2.92,3.90),
                 (1.04,1.98,2.92,3.9,4.9)]:
    memory=9 if len(alphabet)<5 else 8
    starts.append(w.discrete_dp(n,a,b,pairs,alphabet,memory))
for _ in range(700):
    starts.append(rng.choice([1.04,1.98,2.92,3.9,4.9],n-1,p=[.45,.4,.1,.04,.01])+rng.normal(0,.04,n-1))
for i in range(n-1):
    for value in [8,16,32,128,4096]:
        g=np.full(n-1,1.04);g[i]=value;starts.append(g)
upper=(c-sep*(sum(b)-b))/b
findings=[]
for index,g in enumerate(starts):
    fit=minimize(fun,np.clip(g,sep,upper),jac=True,bounds=list(zip(np.full(n-1,sep),upper)),
        method='L-BFGS-B',options={'ftol':1e-14,'gtol':1e-10,'maxiter':500,'maxls':40})
    findings.append((float(fit.fun),fit.x.tolist(),bool(fit.success)))
    if index%200==0:print(index,min(r[0] for r in findings),flush=True)
findings.sort(key=lambda z:z[0]);best=findings[0]
record={'scope':'Numerical adversaries only; no proof of the global floor',
        'candidate':args.candidate.name,'n':n,'separation_lower':sep,
        'proposed_c':c,'starts':len(starts),'ternary_grid_strings':len(samples),
        'smallest_grid_value':float(min(values)),
        'best_observed_minimum':best[0],'gaps':best[1],'margin_to_proposed_c':best[0]-c,
        'coercive_upper_box':upper.tolist(),'elapsed_seconds':time.monotonic()-started,
        'best_30_local_findings':findings[:30]}
(HERE/(args.output_prefix+'.json')).write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='best_30_local_findings'},indent=2))
