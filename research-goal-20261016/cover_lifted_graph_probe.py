"""Lifted w'-graph multi-facet KKT diagnostic on the same fixed eight parents.

The prior midpoint affine slab is retained in both models.  The experiment
adds all supporting slopes of the convex hull of 1/64 derivative rectangles,
then recomputes every intercept over every intersected grid rectangle using
integers.  Scalar variables u_t share all nine gaps and satisfy actual KKT
equations/one-sided boundary conditions.  Floating LP is discovery only;
strict exclusions additionally require rounded nonnegative Farkas weights,
exact DBM flow and payment for all uncancelled u coefficients using |w'|<=7.
"""
from pathlib import Path
from functools import lru_cache
import gzip,hashlib,json,time
import numpy as np
from scipy.optimize import linprog
import cover_curvature_parent_probe as context
g=context.g;SC=g.SC;DS=context.DS;D=g.D;Q=2*SC*DS*D;HERE=Path(__file__).parent
sha=lambda b:hashlib.sha256(b).hexdigest()


def hull(points,upper):
    points=sorted(set(points));stack=[]
    for p in points:
        while len(stack)>1:
            a,b=stack[-2:];cross=(b[0]-a[0])*(p[1]-a[1])-(b[1]-a[1])*(p[0]-a[0])
            if (cross>=0 if upper else cross<=0):stack.pop()
            else:break
        stack.append(p)
    return stack


class GraphOracle:
    def __init__(self,path):
        raw=path.read_bytes();doc=json.loads(raw);self.sha=sha(raw);self.grid=doc['ranges'];self.width=SC//doc['receipt']['grid_step'];self.ds=doc['receipt']['denominator']
        assert self.ds==DS
    @lru_cache(50000)
    def facets(self,l,u):
        if l<0 or u>32*SC:rectangles=[(l,u,-7*DS,7*DS)]
        else:
            first=l//self.width;last=(max(l+1,u)+self.width-1)//self.width
            rectangles=[(max(l,k*self.width),min(u,(k+1)*self.width),*self.grid[k]) for k in range(first,last)]
        upper=[];lower=[]
        for a,b,L,U in rectangles:upper.extend([(a,U),(b,U)]);lower.extend([(a,L),(b,L)])
        slopes={0}
        for points,isupper in [(upper,True),(lower,False)]:
            hh=hull(points,isupper)
            for (x,y),(xx,yy) in zip(hh,hh[1:]):
                if x==xx:continue
                slopes.add(round((yy-y)*SC/(xx-x)))
        rows=[]
        for S in sorted(slopes):
            Cmax=max(SC*U-S*(a if S>=0 else b) for a,b,L,U in rectangles)
            Cmin=min(SC*L-S*(b if S>=0 else a) for a,b,L,U in rectangles)
            rows.extend([(1,S,Cmax),(-1,S,Cmin)])
        return rows,len(rectangles)


def build(state,taylor,graph,add_facets):
    N=len(g.TERMS);V=9+N+9;rows=[];rhs=[];integer=[];meta=[];facets=rectangles=0
    def add(ag,au,B,rindex=None,kind=None):
        row=np.r_[np.array(ag,dtype=float)/Q,np.array(au,dtype=float)/Q,np.zeros(9)]
        if rindex is not None:row[9+N+rindex]=-1
        rows.append(row);rhs.append(B/Q);integer.append((ag,au,B));meta.append(kind)
    for z,(i,j) in enumerate(g.ALL):
        ag=[Q if i<=k<j else 0 for k in range(9)];au=[0]*N
        add(ag,au,2*DS*D*state[1][z],kind=['DBM',z,1]);add([-v for v in ag],au,-2*DS*D*state[0][z],kind=['DBM',z,-1])
    data=[taylor.affine(state[0][g.LOOK[i,j]],state[1][g.LOOK[i,j]]) for i,j,aw in g.TERMS]
    for t,((i,j,aw),(P,m0,m1,err,kind)) in enumerate(zip(g.TERMS,data)):
        for sign in [1,-1]:
            ag=[-sign*2*SC*m1*D if i<=k<j else 0 for k in range(9)];au=[0]*N;au[t]=sign*Q
            B=D*(sign*(2*SC*m0-m1*P)+2*SC*err)
            add(ag,au,B,kind=['slab',t,sign])
        if add_facets:
            z=g.LOOK[i,j];ff,count=graph.facets(state[0][z],state[1][z]);rectangles+=count
            for sign,S,C in ff:
                ag=[-sign*2*SC*S*D if i<=k<j else 0 for k in range(9)];au=[0]*N;au[t]=sign*Q
                add(ag,au,sign*2*D*C,kind=['facet',t,sign,str(S),str(C)]);facets+=1
    for k in range(9):
        for sign in ([1,-1] if state[0][k]>g.SEP else [-1]):
            au=[sign*2*SC*DS*aw if i<=k<j else 0 for i,j,aw in g.TERMS]
            add([0]*9,au,-sign*2*SC*DS*g.BS[k],rindex=k,kind=['KKT',k,sign])
    objective=np.r_[np.zeros(9+N),np.ones(9)]
    return rows,rhs,integer,meta,data,objective,{'facets':facets,'grid_rectangles':rectangles,'rows':len(rows)}


def solve(state,taylor,graph,add_facets):
    rows,rhs,integer,meta,data,obj,stats=build(state,taylor,graph,add_facets);N=len(g.TERMS)
    lp=linprog(obj,A_ub=rows,b_ub=rhs,bounds=[(None,None)]*(9+N)+[(0,None)]*9,method='highs')
    stats.update({'LP_success':bool(lp.success),'L1_residual_hint':float(lp.fun) if lp.success else None})
    if not lp.success or lp.fun<=1e-10:return None,stats,lp
    dual=np.maximum(0.,-np.array(lp.ineqlin.marginals));mx=max(dual)
    if not mx:return None,stats,lp
    closed=g.close(*state);assert closed is not None and closed[:2]==state
    for scale in [2**20,2**32,2**48,2**64]:
        weights=[round(v/mx*scale) for v in dual];ag=[sum(mu*r[0][k] for mu,r in zip(weights,integer)) for k in range(9)]
        au=[sum(mu*r[1][t] for mu,r in zip(weights,integer)) for t in range(N)];B=sum(mu*r[2] for mu,r in zip(weights,integer))
        minimum,flow=g.minimize(0,ag,closed[2]);payment=7*SC*sum(map(abs,au));margin=minimum-payment-SC*B
        if margin>0:
            return {'kind':'lifted_graph_KKT','weighted_rows':[[m,str(mu)] for m,mu in zip(meta,weights) if mu],
              'scalar_affine_data':[[P,str(m0),str(m1),str(err),kind] for P,m0,m1,err,kind in data],
              'gap_coefficients':list(map(str,ag)),'scalar_coefficients':list(map(str,au)),'rhs':str(B),
              'flow':flow,'minimum_numerator':str(minimum),'scalar_residual_payment':str(payment),'strict_margin':str(margin),
              'row_denominator':str(Q),'weight_scale':str(scale)},stats,lp
    return None,stats,lp


def main():
    start=time.monotonic();raw=(HERE/'cover-curvature-parent64.input.json.gz').read_bytes();source=json.loads(gzip.decompress(raw))
    selectionraw=(HERE/'cover-curvature-cut8.json').read_bytes();selection=json.loads(selectionraw);assert selection['receipt']['input_sha256']==sha(raw)
    cases={r['path']:r for r in source['cases']};table=HERE/'cover_newjet.json';oracle=context.curvature.first.TaylorOracle(table);graph=GraphOracle(table)
    rows=[];counts={'parents':0,'baseline_positive':0,'graph_positive':0,'baseline_exact':0,'graph_exact':0,'extra_exact':0}
    for old in selection['rows']:
        path=old['path'];state=tuple(cases[path]['before']);t=time.monotonic();baseline,bs,blp=solve(state,oracle,graph,False);bt=time.monotonic()-t
        t=time.monotonic();graph_result,gs,glp=solve(state,oracle,graph,True);gt=time.monotonic()-t;counts['parents']+=1
        counts['baseline_positive']+=bool(bs['L1_residual_hint'] and bs['L1_residual_hint']>1e-10);counts['graph_positive']+=bool(gs['L1_residual_hint'] and gs['L1_residual_hint']>1e-10)
        counts['baseline_exact']+=bool(baseline);counts['graph_exact']+=bool(graph_result);counts['extra_exact']+=bool(graph_result and not baseline)
        rows.append({'path':path,'baseline_statistics':bs,'graph_statistics':gs,'baseline':baseline,'graph':graph_result,'baseline_seconds':bt,'graph_seconds':gt})
        print(json.dumps({**counts,'baseline_L1':bs['L1_residual_hint'],'graph_L1':gs['L1_residual_hint'],'seconds':time.monotonic()-start}),flush=True)
    out={'receipt':{'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'input_sha256':sha(raw),'selection_sha256':sha(selectionraw),
      'table_sha256':graph.sha,'target':'11/1250','counts':counts,'independent_replay_passed':False,'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start},'rows':rows}
    (HERE/'cover-lifted-graph8.json').write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(out['receipt']),flush=True)
if __name__=='__main__':main()
