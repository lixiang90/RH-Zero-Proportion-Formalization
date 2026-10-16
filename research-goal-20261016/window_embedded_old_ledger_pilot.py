"""One ten-variable ledger lift from the unconditional old nine-point floor.

This changes the pair/pressure ledger while retaining the old actual kernel.
Each old certificate is embedded by deleting one of ten ordered vertices.
The weighted old floors sum directly. Rank capacities are the actual <=2
conditions of WCert.Adm. A numerical LP only selects weights; no new record
is inferred without exact admissibility and the existing counting bridge.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,time
import numpy as np
from scipy.optimize import linprog
from window_kernel_floor_transfer_design import parse_old,LOCAL,FINAL,SITE

HERE=Path(__file__).resolve().parent
OUT=HERE/'window-embedded-old-ledger-pilot.json'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    assert not OUT.exists();started=time.monotonic()
    watched=[Path(__file__),LOCAL,FINAL,SITE,HERE/'window_kernel_floor_transfer_design.py']
    guards={p.name:sha(p) for p in watched}
    old=parse_old(LOCAL);c=old['c'];H=F(6721684105641188747759983512104999330646,10**40)
    website=F(34191001116882886388531117129201664,50760020691785094633026544189453125)
    target=website+F(1,100000);columns=[];pressures=[];embeddings=[]
    for deleted in range(10):
        vertices=[i for i in range(10) if i!=deleted]
        ranks=[F(0)]*9;b=[F(0)]*9;edges=[]
        for (i,j),a in old['a'].items():
            u,v=vertices[i],vertices[j];ranks[v-u-1]+=a;edges.append([u,v,str(a)])
        for r,p in enumerate(old['b']):
            for s in range(vertices[r],vertices[r+1]):b[s]+=p
        columns.append(ranks);pressures.append(sum(b))
        embeddings.append({'deleted':deleted,'vertices':vertices,'pair_weights':edges,
            'pressure':list(map(str,b)),'rank_masses':list(map(str,ranks))})
    A=np.array([[float(columns[j][i]) for j in range(10)] for i in range(9)])
    objective=np.array([float(target*c-B) for B in pressures])
    fit=linprog(-objective,A_ub=A,b_ub=np.full(9,2.),bounds=[(0,None)]*10,
        method='highs-ipm',options={'time_limit':45.})
    out={'scope':__doc__,'source_sha256':guards,'old_floor':str(c),'old_window_H':str(H),
        'target_kappa':str(target),'embeddings':embeddings,'LP_status':int(fit.status),
        'LP_success':bool(fit.success),'actual_new_global_floor_formalized':False,
        'new_zero_proportion_proven':False,'website_submission_ready':False}
    if fit.success:
        lam=list(map(lambda x:F(str(float(x))),fit.x));masses=[sum(columns[j][i]*lam[j] for j in range(10)) for i in range(9)]
        # Downscale rationalized floating weights if any exact capacity exceeds two.
        down=max([F(1)]+[v/2 for v in masses]);lam=[v/down for v in lam]
        masses=[sum(columns[j][i]*lam[j] for j in range(10)) for i in range(9)]
        C=c*sum(lam);B=sum(v*q for v,q in zip(lam,pressures));ratio=(H-B)/(1-C)
        assert all(v>=0 for v in lam) and all(v<=2 for v in masses) and 0<C<F(1,64)
        out.update({'raw_weights':fit.x.tolist(),'rational_weights':list(map(str,lam)),
            'exact_capacity_rescaling':str(down),'new_floor_by_old_floor_sum':str(C),
            'new_pressure':str(B),'new_ratio_formula':str(ratio),'new_ratio_percent_hint':float(100*ratio),
            'strict_target_improvement_exact':ratio>target,'exact_rank_capacity_checks_passed':True,
            'numerical_LP_objective':float(-fit.fun),'required_objective':float(target-H)})
    assert guards=={p.name:sha(p) for p in watched};out['all_sources_unchanged']=True
    out['seconds']=time.monotonic()-started
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k in ['LP_status','new_ratio_percent_hint',
        'strict_target_improvement_exact','rational_weights','seconds']}),flush=True)

if __name__=='__main__':main()
