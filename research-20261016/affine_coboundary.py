"""Uncertified cutting-plane search for type-conditioned affine 7-gap potentials.

Binary boxes cover only [.85,2.5]^8.  Nonlinear optimization is a discovery
oracle, never a lower-bound certificate.  LP output is explicitly provisional.
"""
import argparse, json, time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog,minimize
from scipy.sparse import coo_matrix,hstack,vstack,eye,csr_matrix
import partition_coboundary as part
import periodic_overlap as p

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--rounds',type=int,default=35)
    a=ap.parse_args()
    raw=json.loads(Path(part.__file__).with_suffix('.json').read_text())
    edges=raw['all_edges'];samples=[]
    for e in edges:
        e['bounds']=[(.85,1.5) if w==0 else (1.5,2.5) for w in e['word']]
        e['centre']=np.where(e['word'],1.9726622448599151,1.042254386484171)
        e['x']=np.array(e['gaps'])
        samples.extend([(e['code'],e['x'].copy()),(e['code'],e['centre'].copy())])
    lookup={e['code']:e for e in edges}
    obj=np.zeros(1025);obj[0]=-1
    history=[];st=time.time()
    for round in range(a.rounds):
        rr=[];cc=[];vv=[];bb=[]
        for row,(code,x) in enumerate(samples):
            e=lookup[code];z=x-e['centre']
            rr.append(row);cc.append(0);vv.append(1.)
            for node,v,sgn in [(e['src'],np.r_[1,z[:7]],-1),(e['dst'],np.r_[1,z[1:]],1)]:
                for j in range(8):
                    rr.append(row);cc.append(1+node*8+j);vv.append(sgn*v[j])
            bb.append(part.fg(x)[0])
        mat=coo_matrix((vv,(rr,cc)),shape=(len(samples),1025)).tocsr()
        bounds=[(None,None)]+[(-.02,.02) if j%8==0 else (-.05,.05) for j in range(1024)]
        sol=linprog(obj,A_ub=mat,b_ub=bb,bounds=bounds,method='highs',
            options={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9})
        assert sol.success,sol.message
        target=float(sol.x[0])
        # A minimum-norm representative avoids arbitrary huge state potentials
        # from the highly degenerate maximum-floor LP.
        left=hstack([csr_matrix((1024,1)),eye(1024),-eye(1024)],format='csr')
        right=hstack([csr_matrix((1024,1)),-eye(1024),-eye(1024)],format='csr')
        l1mat=vstack([hstack([mat,csr_matrix((len(samples),1024))]),left,right],format='csr')
        l1obj=np.r_[np.zeros(1025),np.ones(1024)]
        l1sol=linprog(l1obj,A_ub=l1mat,b_ub=np.r_[bb,np.zeros(2048)],
            bounds=[(target-2e-10,None)]+bounds[1:]+[(0,None)]*1024,method='highs',
            options={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9})
        assert l1sol.success,l1sol.message
        theta=l1sol.x[1:1025].reshape(128,8);target=float(l1sol.x[0]);found=[]
        for e in edges:
            src,dst=theta[e['src']],theta[e['dst']]
            lin=np.r_[src[1:],0]-np.r_[0,dst[1:]]
            const=src[0]-dst[0]-lin@e['centre']
            def fg(x):
                f,g=part.fg(x)
                return f+const+lin@x,g+lin
            starts=[e['x'],e['centre'],np.array(e['gaps'])]
            sols=[minimize(fg,x,jac=True,bounds=e['bounds'],method='L-BFGS-B',
                options={'ftol':1e-15,'gtol':1e-10,'maxiter':1000,'maxls':40}) for x in starts]
            best=min(sols,key=lambda s:s.fun);e['x']=best.x
            if best.fun<target-1e-10:
                samples.append((e['code'],best.x.copy()))
            found.append((float(best.fun),e['code'],best.x.tolist()))
        worst=min(found)
        rec={'round':round,'sample_count':len(samples),'lp_target':target,
            'oracle_minimum':worst[0],'gap':target-worst[0],'worst_code':worst[1],
            'conditional_kappa_percent':100*(p.H-p.B)/(1-worst[0]),
            'elapsed_seconds':time.time()-st}
        history.append(rec);print(json.dumps(rec),flush=True)
        out={'status':'uncertified numerical discovery on restricted binary boxes; no new proved bound',
            'source_sha256':p.hashlib.sha256(p.RAW).hexdigest(),'history':history,
            'potential':theta.tolist(),'worst':worst,'samples':len(samples)}
        Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
        if target-worst[0]<2e-10:break

if __name__=='__main__':main()
