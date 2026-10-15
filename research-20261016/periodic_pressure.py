"""Uncertified periodic phase / pressure envelope research, frozen AM kernel."""
import argparse, json, time
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
import periodic_overlap as p

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--max-period',type=int,default=12)
    ap.add_argument('--spans',type=int,default=8)
    ap.add_argument('--pressure-min',type=float,default=.0035)
    ap.add_argument('--pressure-max',type=float,default=.007)
    ap.add_argument('--steps',type=int,default=36)
    ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    a=ap.parse_args()
    phases=[]
    for q in range(1,a.max_period+1):
        for word in p.necklaces(q):
            # Primitive words suffice: repeated phases have exactly same mean.
            if any(q%d==0 and word==word[:d]*(q//d) for d in range(1,q)):
                continue
            phases.append({'period':q,'word':word,'x':np.where(word,1.97,1.04),
                'model':p.Periodic(q,a.spans)})
    results=[]
    start=time.time()
    for pressure in np.linspace(a.pressure_min,a.pressure_max,a.steps):
        p.B=float(pressure)
        runs=[]
        for phase in phases:
            sol=minimize(phase['model'].fg,phase['x'],jac=True,bounds=[(.85,3.5)]*phase['period'],
                method='L-BFGS-B',options={'ftol':1e-15,'gtol':1e-10,'maxiter':600,'maxls':40})
            phase['x']=sol.x
            runs.append({'value':float(sol.fun),'period':phase['period'],
                'word':list(phase['word']),'gaps':sol.x.tolist(),
                'gradient_max':float(np.max(np.abs(sol.jac)))})
        runs.sort(key=lambda r:r['value'])
        best=runs[0]
        rec={'pressure':pressure,'best':best,'top10':runs[:10],
            'conditional_kappa_percent':100*(p.H-pressure)/(1-best['value'])}
        results.append(rec)
        print(json.dumps({k:v for k,v in rec.items() if k!='top10'}),flush=True)
        result={'status':'uncertified periodic candidate upper envelopes; not an achieved lower bound',
            'spans':a.spans,'max_period':a.max_period,'primitive_phases':len(phases),
            'elapsed_seconds':time.time()-start,'results':results}
        a.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')

if __name__=='__main__': main()
