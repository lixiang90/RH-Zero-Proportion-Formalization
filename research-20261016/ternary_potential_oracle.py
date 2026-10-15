"""Uncertified zero-extended binary-affine + ternary-constant potential search.

Each ternary box is optimized locally. Large-gap boxes near a limiting floor
get additional sparse integer starts. No continuous lower bound is certified.
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
    mu=np.array([1.04,1.97]);edges=[];st=time.time();cache={r['code']:r for r in source['all_results']}
    words=list(itertools.product(range(3),repeat=8))
    for ix,word in enumerate(words):
        word=np.array(word);code=sum(int(v)*3**i for i,v in enumerate(word))
        src=code%2187;dst=code//3;large=np.where(word==2)[0]
        srcrow=theta[sum(int(v)<<i for i,v in enumerate(word[:7]))] if not np.any(word[:7]==2) else np.zeros(8)
        dstrow=theta[sum(int(v)<<i for i,v in enumerate(word[1:]))] if not np.any(word[1:]==2) else np.zeros(8)
        lin=np.r_[srcrow[1:],0]-np.r_[0,dstrow[1:]]
        const=srcrow[0]-dstrow[0]
        if not np.any(word[:7]==2):const-=srcrow[1:]@mu[word[:7]]
        if not np.any(word[1:]==2):const+=dstrow[1:]@mu[word[1:]]
        def fg(x):
            f,g=part.fg(x);return f+const+lin@x,g+lin
        if len(large)==0:
            old=cache[sum(int(v)<<i for i,v in enumerate(word))]
            edges.append({'code':code,'src':src,'dst':dst,'word':word.tolist(),
                'value':old['value'],'gaps':old['gaps'],'runs':13,'cached_binary':True})
            continue
        bounds=[[(.85,1.5),(1.5,2.5),(2.5,40)][w] for w in word]
        centre=np.array([1.035,1.965,2.915])[word]
        starts=[centre]
        x=centre.copy();x[large]=3.95;starts.append(x)
        sols=[minimize(fg,x,jac=True,bounds=bounds,method='L-BFGS-B',
            options={'ftol':1e-15,'gtol':1e-10,'maxiter':1000,'maxls':40}) for x in starts]
        sol=min(sols,key=lambda r:r.fun)
        if sol.fun<.0093:
            extra=[]
            for i in large:
                for v in [3.95,5.95,9.95,19.95,31.65]:
                    x=centre.copy();x[i]=v;extra.append(x)
            sols += [minimize(fg,x,jac=True,bounds=bounds,method='L-BFGS-B',
                options={'ftol':1e-15,'gtol':1e-10,'maxiter':1000,'maxls':40}) for x in extra]
            sol=min(sols,key=lambda r:r.fun)
        edges.append({'code':code,'src':src,'dst':dst,'word':word.tolist(),
            'value':float(sol.fun),'gaps':sol.x.tolist(),'runs':len(sols)})
        if ix%512==0:print('boxes',ix,'elapsed',time.time()-st,flush=True)
    rr=[];cc=[];vv=[]
    for i,e in enumerate(edges):
        rr += [i,i,i];cc += [0,1+e['src'],1+e['dst']];vv += [1.,-1.,1.]
    mat=coo_matrix((vv,(rr,cc)),shape=(6561,2188)).tocsr()
    obj=np.r_[-1.,np.zeros(2187)]
    lp=linprog(obj,A_ub=mat,b_ub=[e['value'] for e in edges],bounds=[(None,None)]*2188,method='highs',
        options={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9})
    assert lp.success,lp.message
    target=float(lp.x[0]);flow=-lp.ineqlin.marginals
    left=hstack([csr_matrix((2187,1)),eye(2187),-eye(2187)],format='csr')
    right=hstack([csr_matrix((2187,1)),-eye(2187),-eye(2187)],format='csr')
    mat2=vstack([hstack([mat,csr_matrix((6561,2187))]),left,right],format='csr')
    lp2=linprog(np.r_[np.zeros(2188),np.ones(2187)],A_ub=mat2,
        b_ub=np.r_[[e['value'] for e in edges],np.zeros(4374)],
        bounds=[(target-1e-10,None)]+[(None,None)]*2187+[(0,None)]*2187,method='highs',
        options={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9})
    assert lp2.success,lp2.message
    nums=np.rint(lp2.x[1:2188]*1e12).astype(np.int64)
    out={'status':'uncertified locally optimized arc costs, finite graph LP; no new theorem',
        'input_potential_sha256':hashlib.sha256(raw).hexdigest(),'core_sha256':hashlib.sha256(p.RAW).hexdigest(),
        'gap_partition':[[.85,1.5],[1.5,2.5],[2.5,40]],'binary_base':'zero extended',
        'unrepaired_min':min(e['value'] for e in edges),'graph_minimum_cycle_mean':target,
        'rational_delta_denominator':10**12,'rational_delta_numerators':nums.tolist(),
        'rational_repaired_oracle_min':min(e['value']+(nums[e['src']]-nums[e['dst']])/1e12 for e in edges),
        'nonzero_delta_count':int(np.sum(nums!=0)),
        'active_cycle_edges':[dict(e,flow=float(flow[i])) for i,e in enumerate(edges) if flow[i]>1e-8],
        'edges':edges,'elapsed_seconds':time.time()-st}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['edges','rational_delta_numerators']},indent=2))

if __name__=='__main__':main()
