"""Full epigraph OBBT with support mixtures selected for each span bound.

The energy-minimizing affine minorant need not be best for each coordinate.
For every selected span and sign, a separate LP with the full scalar
epigraph plus energy<c selects a new capacity-valid minorant and a Lagrange
multiplier. The accepted coordinate bounds still use exact integer flows.
This is only discovery; analytic and complete-cover Lean obligations remain.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,gzip,hashlib,json,math,time
import numpy as np
from scipy.optimize import linprog
import cover_sublevel_contractor as old

w=old.w;g=old.g;api=old.api;engine=old.engine;HERE=Path(__file__).parent;K=2**20

def ceil(x):return -((-x.numerator)//x.denominator)

def contract(state,target,axes=None):
    target=int(target);N=len(g.TERMS);rows=[];rhs=[];meta=[]
    for t,(i,j,aw) in enumerate(g.TERMS):
        z=g.LOOK[i,j]
        for C,a,p in g.lines(state[0][z],state[1][z],sum(state[0][i:j])):
            if p==-2:continue
            row=np.zeros(9+N);row[i:j]=a/10**10;row[9+t]=-1
            rows.append(row);rhs.append(-C/g.WD);meta.append((t,C,a,p))
    for z,(i,j) in enumerate(g.ALL):
        row=np.zeros(9+N);row[i:j]=1;rows.extend([row,-row]);rhs.extend([state[1][z]/g.SC,-state[0][z]/g.SC])
    rows.append(np.r_[np.array(g.BS)/g.D,[a/g.D for i,j,a in g.TERMS]]);rhs.append(target/g.DEN)
    cl=g.close(*state);assert cl is not None and cl[:2]==state
    lower=state[0].copy();upper=state[1].copy();certificates=[]
    if axes is None:axes=list(range(9))
    for z in axes:
        i,j=g.ALL[z]
        for sign in [1,-1]:
            objective=np.zeros(9+N);objective[i:j]=sign
            lp=linprog(objective,A_ub=rows,b_ub=rhs,bounds=[(None,None)]*9+[(0,None)]*N,method='highs')
            if not lp.success:continue
            lam=max(0.,-float(lp.ineqlin.marginals[-1]));p=round(lam*K)
            if p<=0 or lam<=0:continue
            weights=[math.floor(max(0.,-float(v))*g.LD/lam) for v in lp.ineqlin.marginals[:len(meta)]]
            for t,(_,_,aw) in enumerate(g.TERMS):
                ids=[k for k,m in enumerate(meta) if m[0]==t];mass=sum(weights[k] for k in ids);cap=aw*(g.LD//g.D)
                if mass>cap:
                    k=max(ids,key=lambda q:weights[q]);assert weights[k]>=mass-cap;weights[k]-=mass-cap
                assert sum(weights[k] for k in ids)<=cap
            C=0;coeff=[b*g.LD for b in g.BS];mixture=[]
            for weight,(t,const,slope,point) in zip(weights,meta):
                if weight<=0:continue
                l,r,_=g.TERMS[t];C+=weight*const
                for k in range(l,r):coeff[k]+=weight*slope
                mixture.append([t,point,str(weight),str(const),str(slope)])
            combined=[p*g.SC*c+(sign*K*g.DEN if i<=r<j else 0) for r,c in enumerate(coeff)]
            value,flow=g.minimize(p*g.SC*C,combined,cl[2])
            bound=F(value-p*g.SC*target,K*g.DEN) if sign==1 else F(p*g.SC*target-value,K*g.DEN)
            newlo=max(lower[z],bound.numerator//bound.denominator) if sign==1 else lower[z]
            newhi=min(upper[z],ceil(bound)) if sign==-1 else upper[z]
            if newlo>lower[z] or newhi<upper[z]:
                lower[z]=newlo;upper[z]=newhi;_,affineflow=g.minimize(C,coeff,cl[2])
                minorant={'lower_bounds':state[0],'upper_bounds':state[1],'mixture_denominator':g.LD,
                  'mixture':mixture,'intercept':str(C),'gap_coefficients':list(map(str,coeff)),'flow':affineflow}
                certificates.append({'axis':z,'sign':sign,'multiplier_numerator':p,'multiplier_denominator':K,
                  'flow':flow,'minimum_numerator':str(value),'bound':str(bound),'new_lower':newlo,'new_upper':newhi,'minorant':minorant})
    if not certificates:return state,[]
    closed=g.close(lower,upper)
    return (None if closed is None else closed[:2]),certificates

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'cover-correlated-direction.input.json.gz')
    ap.add_argument('--sample',type=int,default=1000);ap.add_argument('--output',type=Path,default=HERE/'cover-sublevel-obbt.json');args=ap.parse_args();start=time.monotonic()
    raw=args.input.read_bytes();raw=gzip.decompress(raw) if args.input.suffix=='.gz' else raw;doc=json.loads(raw)
    branches={r['path']:r for r in doc['branches']};paths=sorted(branches)
    selected={paths[k*(len(paths)-1)//max(1,args.sample-1)] for k in range(min(args.sample,len(paths)))}
    needed={p[:k] for p in selected for k in range(1,len(p)+1)};todo=[('r',w.root())];states={}
    while todo:
        path,state=todo.pop()
        if path not in needed:continue
        if path in selected:states[path]=state
        if path in branches:
            r=branches[path]
            for bit,upper in [('1',False),('0',True)]:
                if path+bit in needed:
                    child=g.split(state,r['axis'],r['cut'],upper)
                    if child is not None:todo.append((path+bit,child))
    oracle=api.make_correlated_oracle();results=[];ratios=[]
    counts={'sample':len(states),'already_direction':0,'already_value':0,'contracted':0,'newly_value':0,'newly_direction':0,'empty':0,'coordinate_bounds':0}
    for n,(path,state) in enumerate(sorted(states.items()),1):
        if engine.baseline.exclusion(state,True) or api.correlated_exclusion(state,oracle):counts['already_direction']+=1;continue
        rec=w.certify(state)
        if int(rec.get('floor_numerator','-1'))>=g.TARGET:counts['already_value']+=1;continue
        axes=sorted(set(list(range(9))+[branches[path]['axis']]))
        refined,certificates=contract(state,g.TARGET,axes)
        if certificates:
            counts['contracted']+=1;counts['coordinate_bounds']+=len(certificates);result=None
            if refined is None:counts['empty']+=1;result={'kind':'empty'}
            else:
                ex=api.correlated_exclusion(refined,oracle)
                if ex:counts['newly_direction']+=1;result={'kind':'stationary','result':ex}
                else:
                    rec=w.certify(refined)
                    if int(rec.get('floor_numerator','-1'))>=g.TARGET:counts['newly_value']+=1;result={'kind':'value','result':rec}
                ratio=float(np.prod([(refined[1][i]-refined[0][i]+1)/(state[1][i]-state[0][i]+1) for i in range(9)]));ratios.append(ratio)
            results.append({'path':path,'old_cell':state,'new_cell':refined,'certificates':certificates,'result':result})
        if n%50==0:print(json.dumps({**counts,'done':n,'seconds':time.monotonic()-start}),flush=True)
    receipt={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'api_sources':api.api_sources(oracle),'target_numerator':str(g.TARGET),'counts':counts,'minimum_box_ratio_hint':min(ratios) if ratios else None,
      'median_box_ratio_hint':float(np.median(ratios)) if ratios else None,'ratios_below_half':sum(x<.5 for x in ratios),
      'ratios_below_tenth':sum(x<.1 for x in ratios),'actual_kernel_Lean_bridges_complete':False,'pointwise_cover':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps({'receipt':receipt,'contractions':results},separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
