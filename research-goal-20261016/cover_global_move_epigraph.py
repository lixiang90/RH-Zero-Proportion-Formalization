"""Global competitors with difference hypographs and the energy sublevel.

Several one-sided Taylor upper lines for every affected difference h_s are
mixed with EXACT full pair capacity. A full epigraph LP selects that upper
mixture, a nonnegative sublevel multiplier, and a capacity-valid energy
minorant A. A single exact integer flow certifies
F(g+delta)-F(g)+lambda*(c-A(g))<0 throughout the cell.
The LP is solely a witness selector; all acceptance arithmetic is integral.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,json,math,time
import numpy as np
from scipy.optimize import linprog
import cover_integer_move_concave as concave

base=concave.base;g=base.g;w=base.w;DS=base.DS;SC=g.SC;HERE=Path(__file__).parent;K=2**20

def line_at(oracle,l,u,shift,P):
    if min(l,l+shift*SC)<0 or max(u,u+shift*SC)>32*SC:return None
    v,s=oracle.point(P,shift);r=F(max(P-2*l,2*u-P),2*SC)
    m0=round((v.l+v.u)*DS/2);m1=round((s.l+s.u)*DS/2)
    e0=max(abs(v.l*DS-m0),abs(v.u*DS-m0));e1=max(abs(s.l*DS-m1),abs(s.u*DS-m1))
    B=max(0,oracle.second_range(l,u,shift)[1]);err=base.ceil(e0+e1*r+F(B)*r*r/2)
    return P,m0,m1,err

def exclusion(state,oracle,target,limit=4,statistics=None):
    selected,best=base.candidates(state,oracle,limit);N=len(g.TERMS)
    if statistics is not None:statistics['cells_with_improving_midpoint_move']+=int(bool(selected))
    closed=g.close(*state);assert closed is not None and closed[:2]==state
    for hint,delta in selected:
        affected=[t for t,(i,j,a) in enumerate(g.TERMS) if sum(delta[i:j])]
        M=len(affected);V=9+M+N;A=[];rhs=[];lowermeta=[];uppermeta=[]
        for t,(i,j,aw) in enumerate(g.TERMS):
            z=g.LOOK[i,j]
            for C,slope,p in g.lines(state[0][z],state[1][z],sum(state[0][i:j])):
                if p==-2:continue
                row=np.zeros(V);row[i:j]=slope/10**10;row[9+M+t]=-1
                lowermeta.append((len(A),t,C,slope,p));A.append(row);rhs.append(-C/g.WD)
        valid=True
        for v,t in enumerate(affected):
            i,j,aw=g.TERMS[t];z=g.LOOK[i,j];l,u=state[0][z],state[1][z];shift=sum(delta[i:j])
            if min(l,l+shift*SC)<0 or max(u,u+shift*SC)>32*SC:valid=False;break
            # A concave difference has global tangent upper bounds at every
            # chosen point. Otherwise several paid Taylor lines remain safe.
            Ps={2*l,2*u,l+u,(3*l+u)//2,(l+3*u)//2}
            for P in sorted(Ps):
                point=line_at(oracle,l,u,shift,P);_,m0,m1,err=point
                row=np.zeros(V);row[i:j]=-m1/DS;row[9+v]=1
                uppermeta.append((len(A),t,point));A.append(row);rhs.append((m0+err-m1*P/(2*SC))/DS)
        if not valid:continue
        for z,(i,j) in enumerate(g.ALL):
            row=np.zeros(V);row[i:j]=1;A.extend([row,-row]);rhs.extend([state[1][z]/SC,-state[0][z]/SC])
        row=np.zeros(V);row[:9]=np.array(g.BS)/g.D;row[9+M:]=[aw/g.D for i,j,aw in g.TERMS]
        energy_index=len(A);A.append(row);rhs.append(target/g.DEN)
        objective=np.zeros(V);objective[9:9+M]=[-g.TERMS[t][2]/g.D for t in affected]
        lp=linprog(objective,A_ub=A,b_ub=rhs,bounds=[(None,None)]*(9+M)+[(0,None)]*N,method='highs')
        pressure=sum(b*d for b,d in zip(g.BS,delta))/g.D
        if not lp.success or pressure-lp.fun>=-1e-10:continue
        if statistics is not None:statistics['LP_strict_improvement_hints']+=1
        dual=lp.ineqlin.marginals;lam=max(0.,-float(dual[energy_index]));p=round(lam*K)
        weights=[math.floor(max(0.,-float(dual[idx]))*g.LD) for idx,t,point in uppermeta]
        for t in affected:
            ids=[k for k,(_,tt,_) in enumerate(uppermeta) if tt==t];cap=g.TERMS[t][2]*(g.LD//g.D);mass=sum(weights[k] for k in ids)
            k=max(ids,key=lambda k:weights[k]);weights[k]+=cap-mass;assert weights[k]>=0
        C=2*SC*DS*(g.LD//g.D)*sum(b*d for b,d in zip(g.BS,delta));E=0;coeff=[0]*9;mixture=[]
        for weight,(_,t,(P,m0,m1,err)) in zip(weights,uppermeta):
            if not weight:continue
            i,j,_=g.TERMS[t];C+=weight*(2*SC*m0-m1*P);E+=2*SC*weight*err
            for k in range(i,j):coeff[k]+=2*weight*m1
            mixture.append([t,P,str(weight),str(m0),str(m1),str(err)])
        energy=None;EC=0;ecoeff=[0]*9
        if p:
            assert lam>0
            energyweights=[math.floor(max(0.,-float(dual[idx]))*g.LD/lam) for idx,t,c,s,p0 in lowermeta]
            for t,(_,_,aw) in enumerate(g.TERMS):
                ids=[k for k,(_,tt,_,_,_) in enumerate(lowermeta) if tt==t];cap=aw*(g.LD//g.D);mass=sum(energyweights[k] for k in ids)
                if mass>cap:
                    k=max(ids,key=lambda k:energyweights[k]);energyweights[k]-=mass-cap;assert energyweights[k]>=0
            ecoeff=[b*g.LD for b in g.BS];emix=[]
            for weight,(_,t,const,slope,p0) in zip(energyweights,lowermeta):
                if not weight:continue
                i,j,_=g.TERMS[t];EC+=weight*const
                for k in range(i,j):ecoeff[k]+=weight*slope
                emix.append([t,p0,str(weight),str(const),str(slope)])
            _,eflow=g.minimize(EC,ecoeff,closed[2])
            energy={'lower_bounds':state[0],'upper_bounds':state[1],'mixture_denominator':g.LD,'mixture':emix,
              'intercept':str(EC),'gap_coefficients':list(map(str,ecoeff)),'flow':eflow}
        den=2*SC*g.LD*DS;ratio=den//g.DEN;assert ratio*g.DEN==den
        combined=[K*c-p*ratio*e for c,e in zip(coeff,ecoeff)];constant=K*C+p*ratio*(target-EC)
        minimum,flow=g.minimize(0,[-v for v in combined],closed[2]);upper=constant+K*E-minimum
        if upper<0:return {'kind':'global_move_epigraph','delta':delta,'difference_mixture_denominator':g.LD,
          'difference_upper_mixture':mixture,'energy_minorant':energy,'energy_multiplier_numerator':p,'energy_multiplier_denominator':K,
          'energy_scale_ratio':ratio,'combined_coefficient':list(map(str,combined)),'combined_constant':str(constant),
          'difference_error':str(K*E),'negative_maximum':str(minimum),'flow':flow,'upper_numerator':str(upper),
          'denominator':str(K*den),'lp_improvement_hint':pressure-float(lp.fun),'midpoint_difference_hint':hint}
    return None

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'cover-sublevel-obbt.json')
    ap.add_argument('--max-cells',type=int,default=300);ap.add_argument('--moves',type=int,default=4)
    ap.add_argument('--output',type=Path,default=HERE/'cover-global-move-epigraph.json');args=ap.parse_args();start=time.monotonic()
    raw=args.input.read_bytes();doc=json.loads(raw);target=int(doc['receipt']['target_numerator'])
    taylor=base.api.make_correlated_oracle();oracle=concave.ConcaveDifferenceOracle(taylor);rows=[]
    known_path=HERE/'cover-integer-move-concave.json';known=json.loads(known_path.read_bytes()) if known_path.exists() else {'exclusions':[]}
    known_paths={r['path'] for r in known['exclusions']}
    counts={'checked_cells':0,'already_closed':0,'already_uniform_move':0,'Newton_paths':0,'cells_with_improving_midpoint_move':0,
      'LP_strict_improvement_hints':0,'strict_joint_global_move_exclusions':0}
    inputs=[r for r in doc['contractions'] if r['result'] is None and r['new_cell'] is not None]
    for original in inputs[:args.max_cells]:
        counts['checked_cells']+=1
        if original['path'] in known_paths:counts['already_uniform_move']+=1;continue
        state=(original['new_cell'][0],original['new_cell'][1]);state,steps,ex=base.newton.contract(state,8,taylor)
        if steps:counts['Newton_paths']+=1
        if state is None or ex or base.first.baseline.exclusion(state,True) or base.api.correlated_exclusion(state,taylor):counts['already_closed']+=1;continue
        rec=w.certify(state)
        if int(rec.get('floor_numerator','-1'))>=target:counts['already_closed']+=1;continue
        result=exclusion(state,oracle,target,args.moves,counts)
        if result:
            counts['strict_joint_global_move_exclusions']+=1;rows.append({'path':original['path'],'cell':state,'newton_steps':steps,'result':result})
        if counts['checked_cells']%25==0:print(json.dumps({**counts,'seconds':time.monotonic()-start}),flush=True)
    receipt={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'concave_source_sha256':hashlib.sha256(Path(concave.__file__).read_bytes()).hexdigest(),'table_sha256':taylor.sha,
      'target_numerator':str(target),'known_uniform_move_sha256':hashlib.sha256(known_path.read_bytes()).hexdigest() if known_path.exists() else None,
      'counts':counts,'move_limit':args.moves,'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,
      'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps({'receipt':receipt,'exclusions':rows},separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
