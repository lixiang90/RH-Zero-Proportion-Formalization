"""Global-competitor OBBT with separate signed-difference hypographs.

Each finite move has one lift for every affected scalar span. Multiple
upper Taylor lines constrain each lift separately; the move condition is
pressure_delta + sum a*lift >= 0. Duals only select exact replay witnesses.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,math,time
import numpy as np
from scipy.optimize import linprog
import cover_global_cut_full_contractor as old
import cover_global_move_epigraph as tangent
g=old.g;w=old.w;base=old.base;HERE=Path(__file__).parent;SC=g.SC;DS=old.DS;K=2**20

def all_candidates(state,oracle,limit):
    lo,hi=state;x=np.array([(lo[k]+hi[k])/(2*g.SC) for k in range(9)])
    ints=[round(v) for v in x];moves=set()
    def add(d):
        if any(d) and all(lo[k]+d[k]*g.SC>=g.SEP for k in range(9)):moves.add(tuple(d))
    for k in range(9):
        for step in [-2,-1,1,2]:
            d=[0]*9;d[k]=step;add(d)
    for k in range(9):
        for j in range(9):
            if j==k:continue
            d=[0]*9;d[k]=1;d[j]=-1;add(d)
    for p in oracle.patterns:add([a-b for a,b in zip(p,ints)])
    def score(d):
        return float(np.dot(np.array(g.BS)/g.D,np.array(d))+sum(aw/g.D*(w.kernel(np.array([sum(x[i:j])+sum(d[i:j])]))[0]-w.kernel(np.array([sum(x[i:j])]))[0]) for i,j,aw in g.TERMS))
    scored=sorted((score(d),d) for d in moves)
    return [(hint,list(d)) for hint,d in scored][:limit],(scored[0][0] if scored else None)


def contract_once(state,target,oracle,limit=24):
    candidates,_=all_candidates(state,oracle,limit);moves=[];lift_count=0
    for hint,delta in candidates:
        data=[]
        for t,(i,j,aw) in enumerate(g.TERMS):
            shift=sum(delta[i:j])
            if not shift:continue
            z=g.LOOK[i,j];l,u=state[0][z],state[1][z]
            if min(l,l+shift*SC)<0 or max(u,u+shift*SC)>32*SC:break
            lines=[]
            for P in sorted({2*l,l+u,2*u,(3*l+u)//2,(l+3*u)//2}):
                lines.append(tangent.line_at(oracle,l,u,shift,P))
            data.append((t,lift_count+len(data),lines))
        else:
            if data:moves.append((delta,data));lift_count+=len(data)
    if not moves:return state,None
    N=len(g.TERMS);V=9+N+lift_count;A=[];rhs=[];energy_meta=[];move_meta=[];upper_meta=[]
    for t,(i,j,aw) in enumerate(g.TERMS):
        z=g.LOOK[i,j]
        for C,slope,p0 in g.lines(state[0][z],state[1][z],sum(state[0][i:j])):
            if p0==-2:continue
            row=np.zeros(V);row[i:j]=slope/10**10;row[9+t]=-1
            energy_meta.append((len(A),t,C,slope,p0));A.append(row);rhs.append(-C/g.WD)
    for v,(delta,data) in enumerate(moves):
        for t,lift,lines in data:
            i,j,aw=g.TERMS[t]
            for P,m0,m1,err in lines:
                row=np.zeros(V);row[i:j]=-m1/DS;row[9+N+lift]=1
                upper_meta.append((len(A),v,t,(P,m0,m1,err)));A.append(row);rhs.append((m0+err-m1*P/(2*SC))/DS)
        row=np.zeros(V)
        for t,lift,lines in data:row[9+N+lift]=-g.TERMS[t][2]/g.D
        move_meta.append(len(A));A.append(row);rhs.append(sum(b*d for b,d in zip(g.BS,delta))/g.D)
    for z,(i,j) in enumerate(g.ALL):
        row=np.zeros(V);row[i:j]=1;A.extend([row,-row]);rhs.extend([state[1][z]/SC,-state[0][z]/SC])
    row=np.zeros(V);row[:9]=np.array(g.BS)/g.D;row[9:9+N]=[aw/g.D for i,j,aw in g.TERMS]
    energy_index=len(A);A.append(row);rhs.append(target/g.DEN)
    closed=g.close(*state);assert closed is not None and closed[:2]==state
    lower=state[0].copy();upper=state[1].copy();certificates=[];den=2*SC*g.LD*DS;ratio=den//g.DEN;assert ratio*g.DEN==den
    for axis in range(9):
        for sign in [1,-1]:
            obj=np.zeros(V);obj[axis]=sign
            lp=linprog(obj,A_ub=A,b_ub=rhs,bounds=[(None,None)]*9+[(0,None)]*N+[(None,None)]*lift_count,method='highs')
            if not lp.success:continue
            dual=lp.ineqlin.marginals;energy_lam=max(0.,-float(dual[energy_index]));p=round(energy_lam*K)
            EC=0;ecoeff=[0]*9;energy=None
            if p:
                weights=[math.floor(max(0.,-float(dual[idx]))*g.LD/energy_lam) for idx,t,C,slope,p0 in energy_meta]
                for t,(_,_,aw) in enumerate(g.TERMS):
                    ids=[k for k,(_,tt,_,_,_) in enumerate(energy_meta) if tt==t];cap=aw*(g.LD//g.D);mass=sum(weights[k] for k in ids)
                    if mass>cap:
                        k=max(ids,key=lambda k:weights[k]);weights[k]-=mass-cap;assert weights[k]>=0
                ecoeff=[b*g.LD for b in g.BS];mix=[]
                for weight,(_,t,C,slope,p0) in zip(weights,energy_meta):
                    if not weight:continue
                    i,j,_=g.TERMS[t];EC+=weight*C
                    for k in range(i,j):ecoeff[k]+=weight*slope
                    mix.append([t,p0,str(weight),str(C),str(slope)])
                _,flow=g.minimize(EC,ecoeff,closed[2]);energy={'lower_bounds':state[0],'upper_bounds':state[1],
                  'mixture_denominator':g.LD,'mixture':mix,'intercept':str(EC),'gap_coefficients':list(map(str,ecoeff)),'flow':flow}
            move_models=[];C=p*SC*ratio*EC;coeff=[p*SC*ratio*e+(sign*K*den if k==axis else 0) for k,e in enumerate(ecoeff)]
            for v,(delta,data) in enumerate(moves):
                lam=max(0.,-float(dual[move_meta[v]]));gamma=round(lam*K)
                if not gamma:continue
                ids=[k for k,(_,vv,_,_) in enumerate(upper_meta) if vv==v]
                weights={k:math.floor(max(0.,-float(dual[upper_meta[k][0]]))*g.LD/lam) for k in ids}
                for t,lift,lines in data:
                    subset=[k for k in ids if upper_meta[k][2]==t];cap=g.TERMS[t][2]*(g.LD//g.D);mass=sum(weights[k] for k in subset)
                    k=max(subset,key=lambda k:weights[k]);weights[k]+=cap-mass;assert weights[k]>=0
                MC=2*SC*DS*(g.LD//g.D)*sum(b*d for b,d in zip(g.BS,delta));ME=0;mc=[0]*9;mix=[]
                for k in ids:
                    weight=weights[k]
                    if not weight:continue
                    _,_,t,(P,m0,m1,err)=upper_meta[k];i,j,aw=g.TERMS[t];MC+=weight*(2*SC*m0-m1*P);ME+=2*SC*weight*err
                    for r in range(i,j):mc[r]+=2*weight*m1
                    mix.append([t,P,str(weight),str(m0),str(m1),str(err)])
                C-=SC*gamma*(MC+ME)
                for r in range(9):coeff[r]-=SC*gamma*mc[r]
                move_models.append({'delta':delta,'multiplier':gamma,'difference_mixture_denominator':g.LD,'difference_upper_mixture':mix})
            minimum,flow=g.minimize(C,coeff,closed[2])
            bound=F(minimum-p*SC*ratio*target,K*den) if sign==1 else F(p*SC*ratio*target-minimum,K*den)
            lo=max(lower[axis],bound.numerator//bound.denominator) if sign==1 else lower[axis]
            hi=min(upper[axis],base.ceil(bound)) if sign==-1 else upper[axis]
            if lo>lower[axis] or hi<upper[axis]:
                lower[axis]=lo;upper[axis]=hi
                certificates.append({'axis':axis,'sign':sign,'multiplier_denominator':K,'energy_multiplier':p,'energy_minorant':energy,
                  'move_models':move_models,'constant':str(C),'coefficient':list(map(str,coeff)),
                  'minimum_numerator':str(minimum),'flow':flow,'bound':str(bound),'new_lower':lo,'new_upper':hi})
    if not certificates:return state,None
    new=g.close(lower,upper);refined=None if new is None else new[:2]
    return refined,{'old_cell':state,'new_cell':refined,'certificates':certificates,
      'semantics':'preserves only original global minima below target; not arbitrary KKT points'}
