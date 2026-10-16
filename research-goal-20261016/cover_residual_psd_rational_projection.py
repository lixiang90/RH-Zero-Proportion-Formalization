"""One exact-rational projection attempt of the saved joint SCS hint.

No solver, precision tuning, new point, or Lean run. Decimalize once,
solve only the nine adjacent derivative KKT and 81 corresponding mixed
KKT identities, then check every retained rational row and finite bound.
Only if those pass, check all 41 normalized residual blocks by exact LDL.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,time
import cover_cross_moment_probe as base
import cover_cross_moment_exact_rows as exact

HERE=Path(__file__).parent;ROOT=HERE.parent;V=464;SC=32768

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def ldl(A):
    n=len(A);L=[[F(int(i==j)) for j in range(n)] for i in range(n)];D=[]
    for j in range(n):
        d=A[j][j]-sum(L[j][k]**2*D[k] for k in range(j))
        if d<=0:return None,None,j,d
        D.append(d)
        for i in range(j+1,n):L[i][j]=(A[i][j]-sum(L[i][k]*L[j][k]*D[k] for k in range(j)))/d
    assert all(A[i][j]==sum(L[i][k]*D[k]*L[j][k] for k in range(n)) for i in range(n) for j in range(n))
    return L,D,None,None

def main():
    tick=time.monotonic();source=HERE/'cover-residual-psd-bregman-full-cone.json';oldpath=HERE/'cover-cross-moment-remaining-six.json'
    closedpath=HERE/'cover-bregman-closed-primal-check.json';slabpath=HERE/'cover-residual-psd-pilot.json';table=HERE/'cover_newjet.json'
    watched=[source,oldpath,closedpath,slabpath,table,Path(__file__),Path(base.__file__),Path(base.old.__file__),Path(exact.__file__),base.g.PAR]
    hashes={p.relative_to(ROOT).as_posix():sha(p) for p in watched}
    saved=json.loads(source.read_text());prior=json.loads(oldpath.read_text())['rows'][0];closed=json.loads(closedpath.read_text());slabs=json.loads(slabpath.read_text())
    assert saved['path']==prior['path']==closed['path']==slabs['path']
    x=list(map(lambda v:F(str(v)),saved['raw_primal'][:V]));assert len(x)==V
    initial=x.copy();state=tuple(prior['cell']);assert all(v>123*SC//128 for v in state[0][:9])
    centers=[F(l+u,2*SC) for l,u in zip(state[0][:9],state[1][:9])];radii=[F(u-l,2*SC) for l,u in zip(state[0][:9],state[1][:9])]
    ys=[(x[i]-centers[i])/radii[i] for i in range(9)]
    terms=base.g.TERMS;adj={i:t for t,(i,j,aw) in enumerate(terms) if j==i+1};assert set(adj)==set(range(9))
    updates=[]
    for r in range(9):
        e=adj[r];aw=terms[e][2];assert aw>0
        value=-(F(base.g.BS[r])+sum(F(a)*x[9+t] for t,(i,j,a) in enumerate(terms) if i<=r<j and t!=e))/aw
        updates.append({'index':9+e,'before':str(x[9+e]),'after':str(value)});x[9+e]=value
    for s in range(9):
        for r in range(9):
            e=adj[r];aw=terms[e][2]
            value=-(F(base.g.BS[r])*ys[s]+sum(F(a)*x[base.qindex(s,t)] for t,(i,j,a) in enumerate(terms) if i<=r<j and t!=e))/aw
            k=base.qindex(s,e);updates.append({'index':k,'before':str(x[k]),'after':str(value)});x[k]=value
    for r in range(9):
        assert F(base.g.BS[r])+sum(F(a)*x[9+t] for t,(i,j,a) in enumerate(terms) if i<=r<j)==0
        for s in range(9):assert F(base.g.BS[r])*ys[s]+sum(F(a)*x[base.qindex(s,t)] for t,(i,j,a) in enumerate(terms) if i<=r<j)==0
    taylor=base.old.context.curvature.first.TaylorOracle(table);graph=base.old.GraphOracle(table)
    rr,bb,integer,meta,data,obj,stats=base.old.build(state,taylor,graph,True)
    assert [[P,str(m0),str(m1),str(err),kind] for P,m0,m1,err,kind in data]==[row['data'] for row in slabs['scalar_slabs']]
    ubounds=[]
    for i,j,aw in terms:
        z=base.g.LOOK[i,j];ff,_=graph.facets(state[0][z],state[1][z])
        ubounds.append((max(F(C,SC*base.old.DS) for sign,S,C in ff if sign==-1 and S==0),
            min(F(C,SC*base.old.DS) for sign,S,C in ff if sign==1 and S==0)))
    packets=[prior['energy_packets'][0],closed['proposed_KKT_energy_packet']]
    model=exact.inputs(state,integer,meta,ubounds,packets);assert len(model['rows'])==43306
    digest=hashlib.sha256();violations=[];minimum=None
    for k,row in enumerate(model['rows']):
        digest.update(json.dumps([sorted((i,str(v)) for i,v in row['coeff'].items()),str(row['bound']),row['meta']],separators=(',',':')).encode())
        slack=row['bound']-sum(a*x[i] for i,a in row['coeff'].items());minimum=slack if minimum is None else min(minimum,slack)
        if slack<0:violations.append({'row_index':k,'meta':row['meta'],'slack':str(slack)})
    bound_violations=[]
    for i,(l,u) in enumerate(model['bounds']):
        if not l<=x[i]<=u:bound_violations.append({'index':i,'value':str(x[i]),'lower':str(l),'upper':str(u)})
    result={'scope':__doc__,'path':prior['path'],'input_sha256_start':hashes,'decimalization':'F(str(float)) exactly once; no precision adjustment',
        'projected_464_rational_moments':list(map(str,x)),'normalized_y':list(map(str,ys)),
        'adjacent_edge_indices':[[r,adj[r]] for r in range(9)],'exact_KKT_updates':updates,
        'exact_first_and_mixed_KKT_equalities_checked':90,'retained_rows_checked':len(model['rows']),
        'retained_row_serialization_sha256':digest.hexdigest(),'minimum_exact_linear_slack':str(minimum),
        'linear_violations':violations,'bound_violations':bound_violations,'rational_LDL_blocks':[],
        'actual_Fw_counterexample':'not_claimed','actual_Lean_exclusion':'not_claimed','global_floor':'not_proven'}
    if violations or bound_violations:
        result['status']='failed_exact_linear_or_box_check';result['PSD_check']='not_attempted_after_linear_failure'
    else:
        for e,slab in enumerate(slabs['scalar_slabs']):
            beta=list(map(F,slab['beta']));eps=F(slab['epsilon']);assert eps>0
            X=[[F(1) for j in range(10)] for i in range(10)]
            for i in range(9):X[0][i+1]=X[i+1][0]=ys[i]
            for s,r in base.PAIRS:X[s+1][r+1]=X[r+1][s+1]=x[base.hindex(s,r)]
            z=[x[9+e]]+[x[base.qindex(s,e)] for s in range(9)];res=[(z[i]-sum(X[i][j]*beta[j] for j in range(10)))/eps for i in range(10)]
            N=[row+[res[i]] for i,row in enumerate(X)]+[res+[F(1)]];L,D,bad,pivot=ldl(N)
            if bad is not None:
                result['status']='failed_exact_PSD_check';result['PSD_failure']={'term':e,'pivot_index':bad,'pivot':str(pivot)};break
            result['rational_LDL_blocks'].append({'term':e,'unit_lower':[[str(v) for v in row] for row in L],'positive_diagonal':list(map(str,D))})
        else:result['status']='strict_exact_feasible_relaxation_point';result['PSD_check']='all_41_strict_positive_LDL'
    final={p.relative_to(ROOT).as_posix():sha(p) for p in watched};assert hashes==final;result['input_sha256_end']=final;result['inputs_unchanged']='yes'
    result['elapsed_milliseconds']=int((time.monotonic()-tick)*1000);out=HERE/'cover-residual-psd-rational-projection.json';assert not out.exists()
    out.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'status':result['status'],'row_count':len(model['rows']),'linear_violations':len(violations),
        'bound_violations':len(bound_violations),'first_violations':violations[:3],'LDL_blocks':len(result['rational_LDL_blocks']),
        'elapsed_milliseconds':result['elapsed_milliseconds']},allow_nan=False),flush=True)

if __name__=='__main__':main()
