"""Separate a nonnegative portfolio of feasible global competitors.

At a global minimum EVERY feasible finite move has nonnegative energy
difference. A nonnegative weighted sum of several move differences and a
sublevel payment is therefore nonnegative. Joint LP infeasibility selects
integer portfolio weights; a single exact flow certifies a contradiction.
This can exploit incompatibility between different moves' worst points.
"""
from pathlib import Path
import argparse,hashlib,json,math,time
import numpy as np
from scipy.optimize import linprog
import cover_integer_move_concave as concave

base=concave.base;g=base.g;w=base.w;SC=g.SC;DS=base.DS;HERE=Path(__file__).parent

def assemble(delta,data):
    C=2*SC*DS*sum(b*d for b,d in zip(g.BS,delta));E=0;coeff=[0]*9
    for t,(P,m0,m1,err) in data:
        i,j,aw=g.TERMS[t];C+=aw*(2*SC*m0-m1*P);E+=2*SC*aw*err
        for k in range(i,j):coeff[k]+=2*aw*m1
    return C,E,coeff

def exclusion(state,oracle,target,limit=12,statistics=None):
    selected,_=base.candidates(state,oracle,limit);models=[];N=len(g.TERMS);V=9+N+1;A=[];rhs=[];meta=[]
    den=2*SC*g.D*DS
    for hint,delta in selected:
        data=[]
        for t,(i,j,aw) in enumerate(g.TERMS):
            shift=sum(delta[i:j])
            if not shift:continue
            z=g.LOOK[i,j];row=oracle.affine(state[0][z],state[1][z],shift)
            if row is None:break
            data.append((t,row))
        else:models.append((delta,data,*assemble(delta,data)))
    if len(models)<2:return None
    for t,(i,j,aw) in enumerate(g.TERMS):
        z=g.LOOK[i,j]
        for C,slope,p0 in g.lines(state[0][z],state[1][z],sum(state[0][i:j])):
            if p0==-2:continue
            row=np.zeros(V);row[i:j]=slope/10**10;row[9+t]=-1
            meta.append((len(A),t,C,slope,p0));A.append(row);rhs.append(-C/g.WD)
    for z,(i,j) in enumerate(g.ALL):
        row=np.zeros(V);row[i:j]=1;A.extend([row,-row]);rhs.extend([state[1][z]/SC,-state[0][z]/SC])
    row=np.r_[np.array(g.BS)/g.D,[aw/g.D for i,j,aw in g.TERMS],0.]
    energy_index=len(A);A.append(row);rhs.append(target/g.DEN);move_indices=[]
    for delta,data,C,E,coeff in models:
        row=np.zeros(V);row[:9]=-np.array(coeff,dtype=float)*SC/den;row[-1]=-1
        move_indices.append(len(A));A.append(row);rhs.append((C+E)/den)
    objective=np.zeros(V);objective[-1]=1
    lp=linprog(objective,A_ub=A,b_ub=rhs,bounds=[(None,None)]*9+[(0,None)]*(N+1),method='highs')
    if not lp.success or lp.fun<1e-10:return None
    if statistics is not None:statistics['LP_portfolio_separations']+=1
    dual=lp.ineqlin.marginals;reals=[max(0.,-float(dual[k])) for k in move_indices];lam=max(0.,-float(dual[energy_index]))
    closed=g.close(*state);assert closed is not None and closed[:2]==state
    for S in [65536,1048576]:
        weights=[round(v*S) for v in reals];p=round(lam*S)
        if not any(weights):continue
        EC=0;ecoeff=[0]*9;energy=None
        if p:
            assert lam>0;ews=[math.floor(max(0.,-float(dual[k]))*g.LD/lam) for k,t,C,a,p0 in meta]
            for t,(_,_,aw) in enumerate(g.TERMS):
                ids=[i for i,(_,tt,_,_,_) in enumerate(meta) if tt==t];cap=aw*(g.LD//g.D);mass=sum(ews[i] for i in ids)
                if mass>cap:
                    i=max(ids,key=lambda i:ews[i]);ews[i]-=mass-cap;assert ews[i]>=0
            ecoeff=[b*g.LD for b in g.BS];mixture=[]
            for weight,(_,t,C,a,p0) in zip(ews,meta):
                if not weight:continue
                i,j,_=g.TERMS[t];EC+=weight*C
                for r in range(i,j):ecoeff[r]+=weight*a
                mixture.append([t,p0,str(weight),str(C),str(a)])
            _,eflow=g.minimize(EC,ecoeff,closed[2]);energy={'lower_bounds':state[0],'upper_bounds':state[1],
              'mixture_denominator':g.LD,'mixture':mixture,'intercept':str(EC),'gap_coefficients':list(map(str,ecoeff)),'flow':eflow}
        C=sum(theta*m[2] for theta,m in zip(weights,models));E=sum(theta*m[3] for theta,m in zip(weights,models))
        coeff=[sum(theta*m[4][r] for theta,m in zip(weights,models)) for r in range(9)]
        ratio=den//g.DEN;assert ratio*g.DEN==den;combined=[a-p*ratio*b for a,b in zip(coeff,ecoeff)];constant=C+p*ratio*(target-EC)
        minimum,flow=g.minimize(0,[-v for v in combined],closed[2]);upper=constant+E-minimum
        if upper<0:
            portfolio=[]
            for theta,(delta,data,_,_,_) in zip(weights,models):
                if theta:portfolio.append({'weight':theta,'delta':delta,'scalar_difference_data':[[t,P,str(m0),str(m1),str(err)] for t,(P,m0,m1,err) in data]})
            return {'kind':'global_move_portfolio','models':portfolio,'energy_multiplier':p,'energy_minorant':energy,'energy_scale_ratio':ratio,
              'combined_coefficient':list(map(str,combined)),'combined_constant':str(constant),'difference_error':str(E),'negative_maximum':str(minimum),
              'flow':flow,'upper_numerator':str(upper),'denominator':str(den),'LP_hint':float(lp.fun),'weight_selection_scale':S}
    return None

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--max-cells',type=int,default=100);ap.add_argument('--moves',type=int,default=12)
    ap.add_argument('--output',type=Path,default=HERE/'cover-global-move-portfolio-pilot.json');args=ap.parse_args();start=time.monotonic()
    raw=(HERE/'cover-sublevel-obbt.json').read_bytes();doc=json.loads(raw);target=int(doc['receipt']['target_numerator'])
    oracle=concave.ConcaveDifferenceOracle(base.api.make_correlated_oracle());known=set()
    for name in ['cover-integer-move-concave.json','cover-global-move-epigraph-pilot.json']:
        known.update(r['path'] for r in json.loads((HERE/name).read_bytes())['exclusions'])
    counts={'checked_cells':0,'known_global_moves':0,'already_closed':0,'LP_portfolio_separations':0,'strict_portfolio_exclusions':0};rows=[]
    inputs=[r for r in doc['contractions'] if r['result'] is None and r['new_cell'] is not None]
    for original in inputs[:args.max_cells]:
        counts['checked_cells']+=1
        if original['path'] in known:counts['known_global_moves']+=1;continue
        state=(original['new_cell'][0],original['new_cell'][1]);state,steps,ex=base.newton.contract(state,8,oracle.taylor)
        if state is None or ex or base.first.baseline.exclusion(state,True) or base.api.correlated_exclusion(state,oracle.taylor):counts['already_closed']+=1;continue
        rec=w.certify(state)
        if int(rec.get('floor_numerator','-1'))>=target:counts['already_closed']+=1;continue
        result=exclusion(state,oracle,target,args.moves,counts)
        if result:
            counts['strict_portfolio_exclusions']+=1;rows.append({'path':original['path'],'cell':state,'newton_steps':steps,'result':result})
        if counts['checked_cells']%25==0:print(json.dumps({**counts,'seconds':time.monotonic()-start}),flush=True)
    receipt={'scope':__doc__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'input_sha256':hashlib.sha256(raw).hexdigest(),
      'target_numerator':str(target),'counts':counts,'move_limit':args.moves,'complete_global_cover':False,'new_zero_proportion_proven':False,
      'actual_analytic_Lean_bridges_complete':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps({'receipt':receipt,'exclusions':rows},separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
