"""OBBT using finite global-competitor cuts U_delta >= 0.

U_delta is an affine upper bound on F(g+delta)-F(g), hence nonnegative at
an ORIGINAL global minimum. It is not a necessary condition for arbitrary
KKT points. LP duals select multipliers for energy and the valid global
cuts; exact flow bounds objective+p*A-sum gamma*U and contracts coordinates.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,json,math,time
import numpy as np
from scipy.optimize import linprog
import cover_global_move_portfolio as family
import cover_compact_codec as codec

base=family.base;concave=family.concave;g=family.g;w=family.w;SC=g.SC;DS=family.DS;HERE=Path(__file__).parent;K=2**20

def contract_once(state,target,oracle,limit=12):
    selected,_=base.candidates(state,oracle,limit);models=[];N=len(g.TERMS);V=9+N;A=[];rhs=[];meta=[];den=2*SC*g.D*DS
    for hint,delta in selected:
        data=[]
        for t,(i,j,aw) in enumerate(g.TERMS):
            shift=sum(delta[i:j])
            if not shift:continue
            z=g.LOOK[i,j];row=oracle.affine(state[0][z],state[1][z],shift)
            if row is None:break
            data.append((t,row))
        else:models.append((delta,data,*family.assemble(delta,data)))
    if not models:return state,None
    for t,(i,j,aw) in enumerate(g.TERMS):
        z=g.LOOK[i,j]
        for C,slope,p0 in g.lines(state[0][z],state[1][z],sum(state[0][i:j])):
            if p0==-2:continue
            row=np.zeros(V);row[i:j]=slope/10**10;row[9+t]=-1
            meta.append((len(A),t,C,slope,p0));A.append(row);rhs.append(-C/g.WD)
    for z,(i,j) in enumerate(g.ALL):
        row=np.zeros(V);row[i:j]=1;A.extend([row,-row]);rhs.extend([state[1][z]/SC,-state[0][z]/SC])
    row=np.r_[np.array(g.BS)/g.D,[aw/g.D for i,j,aw in g.TERMS]];ei=len(A);A.append(row);rhs.append(target/g.DEN);move_indices=[]
    for delta,data,C,E,coeff in models:
        row=np.zeros(V);row[:9]=-np.array(coeff,dtype=float)*SC/den
        move_indices.append(len(A));A.append(row);rhs.append((C+E)/den)
    closed=g.close(*state);assert closed is not None and closed[:2]==state
    lower=state[0].copy();upper=state[1].copy();certificates=[]
    for z in range(9):
        for sign in [1,-1]:
            obj=np.zeros(V);obj[z]=sign
            lp=linprog(obj,A_ub=A,b_ub=rhs,bounds=[(None,None)]*9+[(0,None)]*N,method='highs')
            if not lp.success:continue
            dual=lp.ineqlin.marginals;lam=max(0.,-float(dual[ei]));p=round(lam*K)
            gamma=[round(max(0.,-float(dual[k]))*K) for k in move_indices]
            if not any(gamma):continue
            EC=0;ecoeff=[0]*9;energy=None
            if p:
                assert lam>0;weights=[math.floor(max(0.,-float(dual[idx]))*g.LD/lam) for idx,t,C,a,p0 in meta]
                for t,(_,_,aw) in enumerate(g.TERMS):
                    ids=[k for k,(_,tt,_,_,_) in enumerate(meta) if tt==t];cap=aw*(g.LD//g.D);mass=sum(weights[k] for k in ids)
                    if mass>cap:
                        k=max(ids,key=lambda k:weights[k]);weights[k]-=mass-cap;assert weights[k]>=0
                ecoeff=[b*g.LD for b in g.BS];mix=[]
                for weight,(_,t,C,a,p0) in zip(weights,meta):
                    if not weight:continue
                    i,j,_=g.TERMS[t];EC+=weight*C
                    for k in range(i,j):ecoeff[k]+=weight*a
                    mix.append([t,p0,str(weight),str(C),str(a)])
                _,eflow=g.minimize(EC,ecoeff,closed[2]);energy={'lower_bounds':state[0],'upper_bounds':state[1],
                  'mixture_denominator':g.LD,'mixture':mix,'intercept':str(EC),'gap_coefficients':list(map(str,ecoeff)),'flow':eflow}
            ratio=den//g.DEN;assert ratio*g.DEN==den
            C=p*SC*ratio*EC-SC*sum(v*(m[2]+m[3]) for v,m in zip(gamma,models))
            coeff=[p*SC*ratio*ecoeff[k]-SC*sum(v*m[4][k] for v,m in zip(gamma,models))+(sign*K*den if k==z else 0) for k in range(9)]
            minimum,flow=g.minimize(C,coeff,closed[2])
            bound=F(minimum-p*SC*ratio*target,K*den) if sign==1 else F(p*SC*ratio*target-minimum,K*den)
            lo=max(lower[z],bound.numerator//bound.denominator) if sign==1 else lower[z]
            hi=min(upper[z],base.ceil(bound)) if sign==-1 else upper[z]
            if lo>lower[z] or hi<upper[z]:
                lower[z]=lo;upper[z]=hi;certificates.append({'axis':z,'sign':sign,'multiplier_denominator':K,'energy_multiplier':p,
                  'move_multipliers':gamma,'energy_minorant':energy,'constant':str(C),'coefficient':list(map(str,coeff)),
                  'minimum_numerator':str(minimum),'flow':flow,'bound':str(bound),'new_lower':lo,'new_upper':hi})
    if not certificates:return state,None
    new=g.close(lower,upper);refined=None if new is None else new[:2]
    stored=[{'delta':delta,'scalar_difference_data':[[t,P,str(m0),str(m1),str(err)] for t,(P,m0,m1,err) in data]} for delta,data,C,E,c in models]
    return refined,{'old_cell':state,'new_cell':refined,'models':stored,'certificates':certificates,
      'semantics':'preserves only original global minimizers below target; NOT all KKT points or pointwise coverage'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--sample',type=int,default=50);ap.add_argument('--rounds',type=int,default=2)
    ap.add_argument('--output',type=Path,default=HERE/'cover-global-cut-contractor.json');args=ap.parse_args();start=time.monotonic()
    raw=(HERE/'cover-sublevel-obbt.json').read_bytes();doc=json.loads(raw);target=int(doc['receipt']['target_numerator']);oracle=concave.ConcaveDifferenceOracle(base.api.make_correlated_oracle())
    known=set()
    for name in ['cover-integer-move-concave.json','cover-global-move-epigraph.json']:known.update(r['path'] for r in json.loads((HERE/name).read_bytes())['exclusions'])
    counts={'scanned':0,'eligible':0,'global_cut_paths':0,'global_cut_steps':0,'global_cut_bounds':0,'new_direction_closed':0,'new_value_closed':0,'empty':0};rows=[];ratios=[]
    for original in doc['contractions']:
        if counts['eligible']>=args.sample:break
        if original['result'] is not None or original['new_cell'] is None or original['path'] in known:continue
        counts['scanned']+=1;state=(original['new_cell'][0],original['new_cell'][1]);state,prior,ex=base.newton.contract(state,8,oracle.taylor)
        if state is None or ex or base.first.baseline.exclusion(state,True) or base.api.correlated_exclusion(state,oracle.taylor):continue
        rec=w.certify(state)
        if int(rec.get('floor_numerator','-1'))>=target:continue
        counts['eligible']+=1;initial=state;steps=[];result=None
        for k in range(args.rounds):
            state,step=contract_once(state,target,oracle)
            if step is None:break
            steps.append(step);counts['global_cut_steps']+=1;counts['global_cut_bounds']+=len(step['certificates'])
            if state is None:result={'kind':'empty'};counts['empty']+=1;break
            ex=base.api.correlated_exclusion(state,oracle.taylor)
            if ex:result={'kind':'stationary','result':ex};counts['new_direction_closed']+=1;break
            rec=w.certify(state)
            if int(rec.get('floor_numerator','-1'))>=target:result={'kind':'value','result':rec};counts['new_value_closed']+=1;break
        if steps:
            counts['global_cut_paths']+=1
            ratio=None if state is None else math.prod((state[1][k]-state[0][k]+1)/(initial[1][k]-initial[0][k]+1) for k in range(9))
            if ratio is not None:ratios.append(ratio)
            rows.append({'path':original['path'],'prior_newton_steps':prior,'steps':steps,'result':result,'volume_ratio_hint':ratio})
        if counts['eligible']%10==0:print(json.dumps({**counts,'seconds':time.monotonic()-start}),flush=True)
    out={'receipt':{'scope':__doc__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'input_sha256':hashlib.sha256(raw).hexdigest(),
      'target_numerator':str(target),'counts':counts,'median_volume_ratio_hint':float(np.median(ratios)) if ratios else None,
      'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start},'contractions':rows}
    args.output.write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(out['receipt']),flush=True)
if __name__=='__main__':main()
