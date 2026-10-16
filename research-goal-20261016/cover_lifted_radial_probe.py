"""Floating-only radial KKT/RLT diagnostic on the same eight residual parents.

Orthant complementarity gives sum b_i(g_i-sep) + sum a_t*v_t = 0,
where v_t=(span_t-len_t*sep)*w'(span_t).  Keep every prior lifted graph
constraint, add McCormick envelopes coupling g,u,v, then optionally add
all complete-span rectangle-hull facets for the actual scalar v graph.
No floating result is accepted as a proof and no global job is launched.
"""
from pathlib import Path
import gzip,hashlib,json,time
import numpy as np
from scipy.optimize import linprog
import cover_lifted_graph_probe as graph
g=graph.g;SC=graph.SC;DS=graph.DS;HERE=Path(__file__).parent
sha=lambda b:hashlib.sha256(b).hexdigest()


def rectangles(state,t,oracle):
    i,j,aw=g.TERMS[t];z=g.LOOK[i,j];l,u=state[0][z],state[1][z];sep=(j-i)*g.SEP
    if l<0 or u>32*SC:raw=[(l,u,-7*DS,7*DS)]
    else:
        width=oracle.width;first=l//width;last=(max(l+1,u)+width-1)//width
        raw=[(max(l,k*width),min(u,(k+1)*width),*oracle.grid[k]) for k in range(first,last)]
    out=[]
    for a,b,L,U in raw:
        assert a>=sep;products=[(a-sep)*L,(a-sep)*U,(b-sep)*L,(b-sep)*U]
        out.append((a,b,min(products),max(products)))
    return raw,out


def solve(state,taylor,oracle,graph_v):
    original,oldrhs,integer,meta,data,oldobj,stats=graph.build(state,taylor,oracle,True)
    N=len(g.TERMS);V=9+2*N+9;rows=[np.r_[row[:9+N],np.zeros(N),row[9+N:]] for row in original];rhs=list(oldrhs);vfacets=0
    def add(ag,ui,uc,vi,vc,B):
        row=np.r_[np.array(ag,dtype=float),np.zeros(2*N+9)]
        if ui is not None:row[9+ui]=uc
        if vi is not None:row[9+N+vi]=vc
        rows.append(row);rhs.append(B)
    for t,(i,j,aw) in enumerate(g.TERMS):
        z=g.LOOK[i,j];sep=(j-i)*g.SEP/SC;a=(state[0][z]-(j-i)*g.SEP)/SC;b=(state[1][z]-(j-i)*g.SEP)/SC
        raw,rect=rectangles(state,t,oracle);L=min(r[2] for r in raw)/DS;U=max(r[3] for r in raw)/DS
        ag=lambda slope:[slope if i<=k<j else 0 for k in range(9)]
        add(ag(L),t,a,t,-1,L*sep+a*L);add(ag(U),t,b,t,-1,U*sep+b*U)
        add(ag(-L),t,-b,t,1,-L*sep-b*L);add(ag(-U),t,-a,t,1,-U*sep-a*U)
        if graph_v:
            upper=[];lower=[]
            for aa,bb,vL,vU in rect:upper.extend([(aa,vU),(bb,vU)]);lower.extend([(aa,vL),(bb,vL)])
            slopes={0}
            for points,isupper in [(upper,True),(lower,False)]:
                hh=graph.hull(points,isupper)
                for (x,y),(xx,yy) in zip(hh,hh[1:]):
                    if x!=xx:slopes.add(round((yy-y)/(xx-x)))
            for S in slopes:
                Cmax=max(vU-S*(aa if S>=0 else bb) for aa,bb,vL,vU in rect)
                Cmin=min(vL-S*(bb if S>=0 else aa) for aa,bb,vL,vU in rect)
                add(ag(-S/DS),None,0,t,1,Cmax/(SC*DS));add(ag(S/DS),None,0,t,-1,-Cmin/(SC*DS));vfacets+=2
    radial=np.r_[np.array(g.BS)/g.D,np.zeros(N),[aw/g.D for i,j,aw in g.TERMS],np.zeros(9)];B=(g.SEP/SC)*sum(g.BS)/g.D
    rows.extend([radial,-radial]);rhs.extend([B,-B]);objective=np.r_[np.zeros(9+2*N),np.ones(9)]
    lp=linprog(objective,A_ub=rows,b_ub=rhs,bounds=[(None,None)]*(9+2*N)+[(0,None)]*9,method='highs')
    return {'LP_success':bool(lp.success),'LP_status':int(lp.status),'L1_residual_hint':float(lp.fun) if lp.success else None,
      'positive_or_infeasible_hint':bool((lp.success and lp.fun>1e-10) or lp.status==2),'old_graph_facets':stats['facets'],
      'radial_product_graph_facets':vfacets,'McCormick_rows':4*N,'total_rows':len(rows)}


def main():
    start=time.monotonic();packed=(HERE/'cover-curvature-parent64.input.json.gz').read_bytes();source=json.loads(gzip.decompress(packed));cases={r['path']:r for r in source['cases']}
    selectionraw=(HERE/'cover-lifted-graph-energy8.json').read_bytes();selection=json.loads(selectionraw);assert selection['receipt']['input_sha256']==sha(packed)
    taylor=graph.context.curvature.first.TaylorOracle(HERE/'cover_newjet.json');oracle=graph.GraphOracle(HERE/'cover_newjet.json')
    rows=[];counts={'parents':0,'radial_McCormick_hints':0,'radial_graph_hints':0}
    for selected in selection['rows']:
        path=selected['path'];state=tuple(cases[path]['before']);t=time.monotonic();mc=solve(state,taylor,oracle,False);mt=time.monotonic()-t
        t=time.monotonic();full=solve(state,taylor,oracle,True);ft=time.monotonic()-t;counts['parents']+=1
        counts['radial_McCormick_hints']+=mc['positive_or_infeasible_hint'];counts['radial_graph_hints']+=full['positive_or_infeasible_hint']
        rows.append({'path':path,'radial_McCormick':mc,'radial_graph':full,'McCormick_seconds':mt,'full_seconds':ft})
        print(json.dumps({**counts,'last_McCormick':mc['L1_residual_hint'],'last_full':full['L1_residual_hint'],'seconds':time.monotonic()-start}),flush=True)
    out={'receipt':{'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'input_sha256':sha(packed),'selection_sha256':sha(selectionraw),
      'table_sha256':oracle.sha,'counts':counts,'selection':'exact same eight residual parents as stopped energy pilot; no expansion',
      'floating_diagnostic_only':True,'strict_certificates':0,'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start},'rows':rows}
    (HERE/'cover-lifted-radial8.json').write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(out['receipt']),flush=True)
if __name__=='__main__':main()
