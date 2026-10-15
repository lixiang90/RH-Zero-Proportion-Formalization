"""Probe a changed near-matching threshold using the unchanged nine-point weights."""
import importlib.util
import json
from pathlib import Path
import re
import time
import numpy as np
from scipy.optimize import minimize, differential_evolution

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('spectral_defect_frames',HERE/'spectral_defect_frames.py')
base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
source=(HERE.parent/'GramDefect20261015/Core.lean').read_text(encoding='utf8')
atext=source.split('def aW9 :',1)[1].split('def bW9 :',1)[0]
btext=source.split('def bW9 :',1)[1].split('def W9 :',1)[0]
entries=re.findall(r'\|\s*(\d+),\s*(\d+)\s*=>\s*\((\d+)\s*:\s*ℝ\)\s*/\s*(\d+)',atext)
bentries=re.findall(r'\|\s*(\d+)\s*=>\s*\((\d+)\s*:\s*ℝ\)\s*/\s*(\d+)',btext)
assert len(entries)==36 and len(bentries)==8
weights=np.array([int(v)/int(d) for i,j,v,d in entries])
incidence=np.array([[int(int(i)<=q<int(j)) for q in range(8)] for i,j,v,d in entries])
pressure=np.array([int(v)/int(d) for i,v,d in bentries])
B=float(sum(pressure));upper=.025/pressure
def objective(g):
    distances=incidence@g;k=base.kernel(distances)
    return float(weights@(k*k)+pressure@g),incidence.T@(2*weights*k*base.kernel(distances,True))+pressure

def run():
    started=time.monotonic();rng=np.random.default_rng(6716)
    report={'scope':'Numerical constrained minima; no new theorem or finite certificate',
        'weights':'unchanged RiemannFail.W9','B':B,'coercive_ceiling':.025,'rows':[]}
    previous=[]
    for r in [.8,.85,.9,.92,.93,.94,.95,.955,.96,.965,.97,.975]:
        starts=[np.full(8,d) for d in [r,1.,1.05,1.1,1.5,2.,4.]]+previous
        starts += [np.maximum(r,rng.normal(1.1,.2,8)) for _ in range(120)]
        for i in range(8):
            for d in [2,4,8,16]:
                g=np.full(8,1.05);g[i]=d;starts.append(g)
        findings=[]
        for g in starts:
            result=minimize(objective,np.clip(g,r,upper),jac=True,bounds=list(zip(np.full(8,r),upper)),method='L-BFGS-B',
                            options={'ftol':1e-14,'gtol':1e-10,'maxiter':500})
            findings.append((float(result.fun),result.x))
        de=differential_evolution(lambda g:objective(g)[0],[(r,2)]*8,popsize=10,maxiter=120,tol=1e-9,
            seed=int(r*10000),polish=True)
        findings.append((float(de.fun),de.x));findings.sort(key=lambda t:t[0])
        c,g=findings[0];near=float(base.kernel(r)**2)
        actual=min(c,near)
        row={'r':r,'observed_local_c':c,'near_pair_ceiling_k_r_sq':near,'usable_observed_c':actual,
            'observed_kappa':(base.H-B)/(1-actual),'gain_percentage_points':100*((base.H-B)/(1-actual)-base.CURRENT),
            'gaps':g.tolist(),'searches':len(starts)+1,'DE_minimum':float(de.fun)}
        report['rows'].append(row);report['elapsed_seconds']=time.monotonic()-started
        (HERE/'spectral-separation-scan.json').write_text(json.dumps(report,indent=2)+'\n')
        previous=[v for _,v in findings[:20]]
        print(json.dumps(row),flush=True)
    print('elapsed',time.monotonic()-started)

if __name__=='__main__':run()
