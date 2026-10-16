"""Joint lifted derivative graph and energy sublevel, fixed eight residual parents.

All old graph rows are retained.  Added energy epigraph variables v_t are
nonnegative and dominate the existing rigorous scalar support lines.  The
actual energy budget is an additional row.  Quantized Farkas multipliers
obey exact per-term capacities, leaving nonnegative v coefficients; no
upper bound on actual scalar values is needed.  Remaining u coefficients
are paid using |w'|<=7 and all gap terms share one exact DBM flow.
"""
from pathlib import Path
import gzip,hashlib,json,time
import numpy as np
from scipy.optimize import linprog
import cover_lifted_graph_probe as graph
import cover_energy_gradient_joint as old_joint
g=graph.g;SC=graph.SC;DS=graph.DS;D=graph.D;Q=graph.Q;HERE=Path(__file__).parent
sha=lambda b:hashlib.sha256(b).hexdigest()


def exclusion(state,taylor,oracle,target):
    oldrows,oldrhs,oldint,oldmeta,data,oldobj,stats=graph.build(state,taylor,oracle,True)
    N=len(g.TERMS);V=9+2*N+9;rows=[];rhs=list(oldrhs);integer=[];meta=list(oldmeta);supports=[]
    for row,(ag,au,B) in zip(oldrows,oldint):
        rows.append(np.r_[row[:9+N],np.zeros(N),row[9+N:]])
        integer.append((ag,au,[0]*N,B))
    assert Q%g.WD==0 and Q%g.DEN==0
    for t,(i,j,aw) in enumerate(g.TERMS):
        z=g.LOOK[i,j]
        for C,slope,p0 in g.lines(state[0][z],state[1][z],sum(state[0][i:j])):
            if p0==-2:continue
            ag=[Q//D*slope if i<=k<j else 0 for k in range(9)];au=[0]*N;av=[0]*N;av[t]=-Q;B=-(Q//g.WD)*C
            row=np.r_[np.array(ag,dtype=float)/Q,np.zeros(N),np.array(av,dtype=float)/Q,np.zeros(9)]
            supports.append((len(rows),t));rows.append(row);rhs.append(B/Q);integer.append((ag,au,av,B));meta.append(['energy_support',t,p0,str(C),str(slope)])
    ag=[Q//D*b for b in g.BS];au=[0]*N;av=[Q//D*aw for i,j,aw in g.TERMS];B=(Q//g.DEN)*target
    energy_index=len(rows);rows.append(np.r_[np.array(ag,dtype=float)/Q,np.zeros(N),np.array(av,dtype=float)/Q,np.zeros(9)]);rhs.append(B/Q)
    integer.append((ag,au,av,B));meta.append(['energy_sublevel'])
    objective=np.r_[np.zeros(9+2*N),np.ones(9)]
    lp=linprog(objective,A_ub=rows,b_ub=rhs,bounds=[(None,None)]*(9+N)+[(0,None)]*(N+9),method='highs')
    stats.update({'energy_support_rows':len(supports),'total_rows':len(rows),'LP_success':bool(lp.success),'L1_residual_hint':float(lp.fun) if lp.success else None})
    if not lp.success or lp.fun<=1e-10:return None,stats
    real=np.maximum(0.,-np.array(lp.ineqlin.marginals));mx=max(real);cl=g.close(*state);assert cl is not None and cl[:2]==state
    for scale in [2**20,2**32,2**48,2**64,2**80]:
        weights=[round(v/mx*scale) for v in real];energy_mu=weights[energy_index]
        for t,(_,_,aw) in enumerate(g.TERMS):
            ids=[i for i,tt in supports if tt==t];cap=energy_mu*aw//D;excess=sum(weights[i] for i in ids)-cap
            for i in sorted(ids,key=lambda i:weights[i],reverse=True):
                if excess<=0:break
                take=min(weights[i],excess);weights[i]-=take;excess-=take
            assert sum(weights[i] for i in ids)<=cap
        ag=[sum(mu*r[0][k] for mu,r in zip(weights,integer)) for k in range(9)]
        au=[sum(mu*r[1][t] for mu,r in zip(weights,integer)) for t in range(N)]
        av=[sum(mu*r[2][t] for mu,r in zip(weights,integer)) for t in range(N)];assert min(av)>=0
        B=sum(mu*r[3] for mu,r in zip(weights,integer));minimum,flow=g.minimize(0,ag,cl[2]);payment=7*SC*sum(map(abs,au));margin=minimum-payment-SC*B
        if margin>0:
            return {'kind':'lifted_graph_energy_KKT','weighted_rows':[[m,str(mu)] for m,mu in zip(meta,weights) if mu],
              'scalar_affine_data':[[P,str(m0),str(m1),str(err),kind] for P,m0,m1,err,kind in data],
              'gap_coefficients':list(map(str,ag)),'scalar_coefficients':list(map(str,au)),'value_coefficients':list(map(str,av)),'rhs':str(B),
              'flow':flow,'minimum_numerator':str(minimum),'scalar_residual_payment':str(payment),'strict_margin':str(margin),
              'row_denominator':str(Q),'weight_scale':str(scale),'energy_multiplier':str(energy_mu)},stats
    return None,stats


def main():
    start=time.monotonic();raw=(HERE/'cover-curvature-parent64.input.json.gz').read_bytes();source=json.loads(gzip.decompress(raw))
    graphraw=(HERE/'cover-lifted-graph64.json').read_bytes();old=json.loads(graphraw);assert old['receipt']['input_sha256']==sha(raw)
    closed={r['path'] for r in old['rows'] if r['graph']};selected=[r for r in source['cases'] if r['path'] not in closed][:8]
    taylor=graph.context.curvature.first.TaylorOracle(HERE/'cover_newjet.json');oracle=graph.GraphOracle(HERE/'cover_newjet.json')
    rows=[];counts={'parents':0,'old_joint_closed':0,'graph_energy_positive':0,'graph_energy_exact':0,'new_only_closed':0}
    for case in selected:
        state=tuple(case['before']);t=time.monotonic();baseline=old_joint.exclusion(state,taylor,g.TARGET);bt=time.monotonic()-t
        t=time.monotonic();result,stats=exclusion(state,taylor,oracle,g.TARGET);gt=time.monotonic()-t;counts['parents']+=1
        counts['old_joint_closed']+=bool(baseline);counts['graph_energy_positive']+=bool(stats['L1_residual_hint'] and stats['L1_residual_hint']>1e-10)
        counts['graph_energy_exact']+=bool(result);counts['new_only_closed']+=bool(result and not baseline)
        rows.append({'path':case['path'],'old_joint':baseline,'joint_statistics':stats,'joint':result,'old_joint_seconds':bt,'joint_seconds':gt})
        print(json.dumps({**counts,'L1_residual_hint':stats['L1_residual_hint'],'seconds':time.monotonic()-start}),flush=True)
    out={'receipt':{'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'engine_sha256':sha(Path(graph.__file__).read_bytes()),
      'input_sha256':sha(raw),'graph64_sha256':sha(graphraw),'table_sha256':oracle.sha,'target':'11/1250',
      'selection':'first8 in frozen discovery-order parent64 not among the13 graph-only closures',
      'counts':counts,'independent_replay_passed':False,'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start},'rows':rows}
    (HERE/'cover-lifted-graph-energy8.json').write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(out['receipt']),flush=True)
if __name__=='__main__':main()
