"""Exact-flow hull contraction from an energy minorant and F < c.

Every retained sublevel point satisfies A(q)=C+a.q < TARGET. For p>=0,
an exact flow lower bound m for s*K*DEN*z+p*SC*A gives an outward bound
on span z. Floating LP only selects p/K; all accepted bounds are integer
flow inequalities. This preserves sublevel points, not every cell point.
Actual scalar minorants and the final complete minimizer cover remain Lean
obligations. No new zeta proportion is asserted by this experiment.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,gzip,hashlib,json,time
import numpy as np
from scipy.optimize import linprog
import cover_correlated_api as api
import cover_correlated_direction as engine

w=engine.w;g=w.g;HERE=Path(__file__).parent;K=2**20

def ceil(x):return -((-x.numerator)//x.denominator)

def contract_minorant(state,minorant,axes=None):
    """Return refined cell and arithmetic certificates; no optimizer trusted."""
    C=int(minorant['intercept']);coeff=list(map(int,minorant['gap_coefficients']))
    cl=g.close(*state);assert cl is not None and cl[:2]==state
    rows=[];rhs=[]
    for z,(i,j) in enumerate(g.ALL):
        row=np.zeros(9);row[i:j]=1;rows.extend([row,-row]);rhs.extend([state[1][z]/g.SC,-state[0][z]/g.SC])
    rows.append(np.array(coeff,dtype=float)*g.SC/g.DEN);rhs.append((g.TARGET-C)/g.DEN)
    lower=state[0].copy();upper=state[1].copy();certificates=[]
    if axes is None:axes=list(range(9))
    for z in axes:
        i,j=g.ALL[z]
        for sign in [1,-1]:
            objective=np.zeros(9);objective[i:j]=sign
            lp=linprog(objective,A_ub=rows,b_ub=rhs,bounds=[(None,None)]*9,method='highs')
            if not lp.success:continue
            multiplier=max(0.,-float(lp.ineqlin.marginals[-1]));p=round(multiplier*K)
            if p<=0:continue
            combined=[p*g.SC*c+(sign*K*g.DEN if i<=r<j else 0) for r,c in enumerate(coeff)]
            value,flow=g.minimize(p*g.SC*C,combined,cl[2])
            bound=F(value-p*g.SC*g.TARGET,K*g.DEN) if sign==1 else F(p*g.SC*g.TARGET-value,K*g.DEN)
            newlo=max(lower[z],bound.numerator//bound.denominator) if sign==1 else lower[z]
            newhi=min(upper[z],ceil(bound)) if sign==-1 else upper[z]
            if newlo>lower[z] or newhi<upper[z]:
                lower[z]=newlo;upper[z]=newhi
                certificates.append({'axis':z,'sign':sign,'multiplier_numerator':p,'multiplier_denominator':K,
                  'flow':flow,'minimum_numerator':str(value),'bound':str(bound),'new_lower':newlo,'new_upper':newhi})
    if not certificates:return state,[]
    closed=g.close(lower,upper)
    return (None if closed is None else closed[:2]),certificates

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'cover-correlated-direction.input.json.gz')
    ap.add_argument('--sample',type=int,default=1000);ap.add_argument('--all-spans',action='store_true')
    ap.add_argument('--iterations',type=int,default=1);ap.add_argument('--output',type=Path,default=HERE/'cover-sublevel-contractor.json');args=ap.parse_args();start=time.monotonic()
    raw=args.input.read_bytes();raw=gzip.decompress(raw) if args.input.suffix=='.gz' else raw;doc=json.loads(raw)
    branches={r['path']:r for r in doc['branches']};paths=sorted(branches)
    selected={paths[k*(len(paths)-1)//max(1,args.sample-1)] for k in range(min(args.sample,len(paths)))}
    needed={p[:k] for p in selected for k in range(1,len(p)+1)};todo=[('r',w.root())];states={}
    while todo:
        p,s=todo.pop()
        if p not in needed:continue
        if p in selected:states[p]=s
        if p in branches:
            r=branches[p]
            for bit,upper in [('1',False),('0',True)]:
                if p+bit in needed:
                    child=g.split(s,r['axis'],r['cut'],upper)
                    if child is not None:todo.append((p+bit,child))
    oracle=api.make_correlated_oracle();results=[];ratios=[]
    counts={'sample':len(states),'already_direction':0,'already_value':0,'contracted':0,'newly_value':0,'newly_direction':0,'empty':0,'coordinate_bounds':0}
    for n,(path,original) in enumerate(sorted(states.items()),1):
        if engine.baseline.exclusion(original,True) or api.correlated_exclusion(original,oracle):counts['already_direction']+=1;continue
        state=original;steps=[];result=None
        for iteration in range(args.iterations):
            rec=w.certify(state)
            if int(rec.get('floor_numerator','-1'))>=g.TARGET:
                if iteration==0:counts['already_value']+=1
                else:counts['newly_value']+=1;result={'kind':'value','result':rec}
                break
            assert 'certificate' in rec
            axes=list(range(45)) if args.all_spans else sorted(set(list(range(9))+[branches[path]['axis']]))
            refined,certificates=contract_minorant(state,rec['certificate'],axes)
            if not certificates:break
            steps.append({'old_cell':state,'new_cell':refined,'minorant':rec['certificate'],'certificates':certificates});state=refined
            counts['coordinate_bounds']+=len(certificates)
            if state is None:counts['empty']+=1;result={'kind':'empty'};break
            ex=api.correlated_exclusion(state,oracle)
            if ex:counts['newly_direction']+=1;result={'kind':'stationary','result':ex};break
        if steps:
            counts['contracted']+=1
            if result is None and state is not None:
                rec=w.certify(state)
                if int(rec.get('floor_numerator','-1'))>=g.TARGET:counts['newly_value']+=1;result={'kind':'value','result':rec}
            ratio=None if state is None else float(np.prod([(state[1][i]-state[0][i]+1)/(original[1][i]-original[0][i]+1) for i in range(9)]))
            if ratio is not None:ratios.append(ratio)
            results.append({'path':path,'steps':steps,'result':result,'box_volume_ratio_hint':ratio})
        if n%50==0:print(json.dumps({**counts,'done':n,'seconds':time.monotonic()-start}),flush=True)
    receipt={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'api_sources':api.api_sources(oracle),'counts':counts,'iterations':args.iterations,'all_spans':args.all_spans,
      'minimum_box_ratio_hint':min(ratios) if ratios else None,'median_box_ratio_hint':float(np.median(ratios)) if ratios else None,
      'ratios_below_half':sum(x<.5 for x in ratios),'ratios_below_tenth':sum(x<.1 for x in ratios),
      'sublevel_contraction_Lean_proven':False,'pointwise_cover':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps({'receipt':receipt,'contractions':results},separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
