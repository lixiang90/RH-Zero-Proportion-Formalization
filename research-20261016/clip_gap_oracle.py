"""Uncertified full high-gap search plus constant de Bruijn potential repair.

The 128-state affine potential is clipped at gap 2.5.  Each high-gap box is
searched at all 2/3 patterns and additional sparse large-gap starts.  This is
an adversarial discovery oracle, never a continuous certificate.
"""
import hashlib,itertools,json,time
from pathlib import Path
import numpy as np
from scipy.optimize import minimize,linprog
from scipy.sparse import coo_matrix,hstack,vstack,eye,csr_matrix
import periodic_overlap as p
import partition_coboundary as part

def main():
    inp=Path(__file__).with_name('validate_affine_potential.json');raw=inp.read_bytes();source=json.loads(raw)
    theta=np.zeros((128,8))
    for s,row in source['potential_numerators'].items():theta[int(s)]=np.array(row)/source['denominator']
    mu=np.array([1.04,1.97]);edges=[];st=time.time()
    for word in itertools.product(range(2),repeat=8):
        word=np.array(word);code=sum(int(v)<<i for i,v in enumerate(word));src=code&127;dst=code>>1
        lin=np.r_[theta[src,1:],0]-np.r_[0,theta[dst,1:]]
        const=theta[src,0]-theta[dst,0]-lin@mu[word]
        def fg(x):
            f,g=part.fg(x);clipped=np.minimum(x,2.5)
            return f+const+lin@clipped,g+lin*(x<=2.5)
        bounds=[(.85,1.5) if w==0 else (1.5,40) for w in word]
        high=np.where(word)[0]
        starts=[]
        for levels in itertools.product([1.965,2.915],repeat=len(high)):
            x=np.full(8,1.035);x[high]=levels;starts.append(x)
        for i in high:
            for v in [3.95,5.95,9.95,19.95,31.65]:
                x=np.where(word,1.965,1.035);x[i]=v;starts.append(x)
        sols=[minimize(fg,x,jac=True,bounds=bounds,method='L-BFGS-B',
            options={'ftol':1e-15,'gtol':1e-10,'maxiter':1000,'maxls':40}) for x in starts]
        sol=min(sols,key=lambda r:r.fun)
        edges.append({'code':code,'src':src,'dst':dst,'value':float(sol.fun),'gaps':sol.x.tolist(),'runs':len(starts)})
        if len(edges)%32==0:print('boxes',len(edges),'elapsed',time.time()-st,flush=True)
    mat=np.zeros((256,129))
    for i,e in enumerate(edges):
        mat[i,0]=1;mat[i,1+e['src']]-=1;mat[i,1+e['dst']]+=1
    obj=np.r_[-1.,np.zeros(128)]
    lp=linprog(obj,A_ub=mat,b_ub=[e['value'] for e in edges],bounds=[(None,None)]*129,method='highs')
    assert lp.success,lp.message
    target=float(lp.x[0]);flow=-lp.ineqlin.marginals
    # Minimal L1 representative at the maximum graph floor (up to tiny slack).
    mat=csr_matrix(mat)
    left=hstack([csr_matrix((128,1)),eye(128),-eye(128)],format='csr')
    right=hstack([csr_matrix((128,1)),-eye(128),-eye(128)],format='csr')
    mat2=vstack([hstack([mat,csr_matrix((256,128))]),left,right],format='csr')
    obj2=np.r_[np.zeros(129),np.ones(128)]
    lp2=linprog(obj2,A_ub=mat2,b_ub=np.r_[[e['value'] for e in edges],np.zeros(256)],
        bounds=[(target-1e-10,None)]+[(None,None)]*128+[(0,None)]*128,method='highs',
        options={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9})
    assert lp2.success,lp2.message
    delta=lp2.x[1:129];nums=np.rint(delta*1e12).astype(np.int64)
    out={'status':'uncertified adversarial local search and finite graph LP; no proved continuous bound',
        'input_potential_sha256':hashlib.sha256(raw).hexdigest(),'core_sha256':hashlib.sha256(p.RAW).hexdigest(),
        'gap_partition':[[.85,1.5],[1.5,40]],'clip_upper':2.5,
        'unrepaired_min':min(e['value'] for e in edges),'graph_minimum_cycle_mean':target,
        'rational_delta_denominator':10**12,'rational_delta_numerators':nums.tolist(),
        'rational_repaired_oracle_min':min(e['value']+(nums[e['src']]-nums[e['dst']])/1e12 for e in edges),
        'active_cycle_edges':[dict(e,flow=float(flow[i])) for i,e in enumerate(edges) if flow[i]>1e-8],
        'edges':edges,'elapsed_seconds':time.time()-st}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['edges','rational_delta_numerators']},indent=2))

if __name__=='__main__':main()
