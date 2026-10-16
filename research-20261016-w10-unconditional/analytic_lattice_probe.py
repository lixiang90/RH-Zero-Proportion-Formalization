"""Floating evidence for joint convexity on coherent lattice chambers.

The generic Taylor lower-bound lemma in the accompanying note is valid,
but scalar curvature extrema below are only sampled. No interval theorem,
coverage theorem, or unconditional zeta lower bound is asserted here.
"""
from pathlib import Path
import hashlib,json,sys,time
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0,str(Path(__file__).parent))
import analytic_memory_probe as m

HERE=Path(__file__).parent;ROOT=HERE.parent

def d2sinc(z):
    out=np.empty_like(z);small=np.abs(z)<1e-3;t=z[small]
    out[small]=-np.pi**2/3+np.pi**4*t*t/10-np.pi**6*t**4/168
    t=z[~small];out[~small]=-np.pi*np.sin(np.pi*t)/t-2*np.cos(np.pi*t)/(t*t)+2*np.sin(np.pi*t)/(np.pi*t**3)
    return out

def w2(x):
    k,dk=m.amplitude(x);u=x[:,None]+m.FREQ;v=x[:,None]-m.FREQ
    ddk=(d2sinc(u)+d2sinc(v))@m.COEF/(2*m.NORM)
    return 2*(dk*dk+k*ddk)

def chamber_key(x):
    return tuple(map(int,np.diff(np.rint(np.r_[0.,np.cumsum(x)]).astype(int))))

def phase_width(x):
    q=np.r_[0.,np.cumsum(x)];d=q-np.rint(q)
    return float(max(d)-min(d)),d

def main():
    start=time.monotonic();path=ROOT/'research-20261016/spectral-wcert-reopt-full-ternary-samples-n10.npz'
    source=np.load(path);g=source['gaps'];pairs=[(i,j) for i in range(10) for j in range(i+1,10)]
    aa=np.array([next((v for u,vv,v in m.TERMS if (u,vv)==(i,j)),0.) for i,j in pairs])
    values=g@m.B+source['features']@aa
    records={}
    for x,val in zip(g,values):
        if val>.00871:continue
        key=chamber_key(x)
        if key not in records or val<records[key][1]:records[key]=(x,float(val))
    # x_j = integer_j + u_j; u_0=0 and all u_j in [-.105,.105]
    # implies every distance lies in its integer center +/- .21.
    curv={n:float(min(w2(np.linspace(n-.21,n+.21,4097)))) for n in range(1,45)}
    results=[]
    for key,(seed,val) in sorted(records.items(),key=lambda p:p[1][1]):
        fit=minimize(lambda x:m.objective(x,9),seed,jac=True,method='L-BFGS-B',
            bounds=[(.85,30)]*9,options={'maxiter':500,'ftol':2e-15,'gtol':1e-11})
        # A rational anchor: q_r = integer / 2^20.
        anchor=np.rint(fit.x*2**20)/2**20;value,grad=m.objective(anchor,9)
        centers=np.rint(m.INC@anchor).astype(int)
        matrix=m.INC.T@((m.A*np.array([curv[int(n)] for n in centers]))[:,None]*m.INC)
        eig=float(np.linalg.eigvalsh(matrix)[0]);penalty=float(grad@np.linalg.solve(matrix,grad)/2)
        width,phase=phase_width(anchor)
        results.append({'integer_gaps':list(key),'anchor_numerators':np.rint(anchor*2**20).astype(int).tolist(),
            'anchor_denominator':2**20,'anchor_float_value':value,'gradient':grad.tolist(),
            'sampled_hessian_lower_eigenvalue':eig,'hypothetical_strong_convexity_penalty':penalty,
            'hypothetical_whole_chamber_lower_bound':value-penalty,
            'prefix_phase_width':width,'prefix_phase_range':[float(min(phase)),float(max(phase))],
            'anchor_in_fixed_chamber':bool(min(phase)>=-.105 and max(phase)<=.105),
            'curvature_minima_sampled_only':True})
    thresholds=[]
    for threshold in [.00867,.00868,.00869,.0087,.00871]:
        subset=g[values<=threshold]
        widths=[phase_width(x)[0] for x in subset]
        thresholds.append({'floating_objective_threshold':threshold,'sample_count':len(subset),
            'max_prefix_phase_width':max(widths,default=None),
            'integer_patterns':len({chamber_key(x) for x in subset})})
    result={'scope':__doc__,'parameter_sha256':hashlib.sha256(m.PARAM.read_bytes()).hexdigest(),
        'sample_archive_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'sample_count':len(g),'threshold_statistics':thresholds,
        'scalar_chamber_radius':.21,'point_phase_radius':.105,
        'sampled_scalar_curvature_lower_bounds':curv,
        'all_scalar_curvature_samples_positive':bool(min(curv.values())>0),
        'tested_chambers':len(results),'min_hypothetical_chamber_lower_bound':min(z['hypothetical_whole_chamber_lower_bound'] for z in results),
        'results':results,'seconds':time.monotonic()-start,
        'formal_scalar_curvature_proven':False,'global_chamber_coverage_proven':False,
        'new_unconditional_bound_proven':False}
    (HERE/'analytic_lattice_probe.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in result.items() if k not in ['results','sampled_scalar_curvature_lower_bounds']}),flush=True)

if __name__=='__main__':main()
