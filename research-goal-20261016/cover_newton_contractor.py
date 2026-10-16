"""Integer-flow interval-Newton contraction for KKT-compatible minima.

At an interior coordinate face any linear combination of the corresponding
partial derivatives is zero. Approximate inverse-Hessian rows only SELECT
integer combinations. Exact affine Taylor data plus graph-flow upper/lower
bounds then shrink coordinate intervals without discarding a possible KKT
point. This experiment is not a Lean minimizer-cover proof.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse, gzip, hashlib, json, math, time
import numpy as np
import cover_correlated_direction as engine
import cover_correlated_api as api
g=engine.g;w=engine.w;HERE=Path(__file__).parent

def ceil(x):return -((-x.numerator)//x.denominator)

def contract_once(state,oracle):
    free=[i for i in range(9) if state[0][i]>g.SEP]
    if not free:return state,[]
    data=[oracle.affine(state[0][g.LOOK[i,j]],state[1][g.LOOK[i,j]]) for i,j,a in g.TERMS]
    H=np.zeros((9,9))
    for (i,j,a),(P,m0,m1,err,kind) in zip(g.TERMS,data):H[i:j,i:j]+=(a/g.D)*(m1/engine.DS)
    block=H[np.ix_(free,free)]
    try:inverse=np.linalg.inv(block)
    except np.linalg.LinAlgError:return state,[]
    if not np.all(np.isfinite(inverse)):return state,[]
    lower=state[0].copy();upper=state[1].copy();certificates=[];cl=g.close(*state);assert cl is not None and cl[:2]==state
    for k,i in enumerate(free):
        row=inverse[k];scale=max(abs(v) for v in row)
        if scale==0:continue
        direction=[0]*9
        for q,j in enumerate(free):direction[j]=round(row[q]/scale*65536)
        _,record=engine.exact_upper(state,data,direction)
        coeff=list(map(int,record['coefficient']));C=int(record['constant']);E=int(record['error'])
        if coeff[i]<0:
            direction=[-v for v in direction];C=-C;coeff=[-v for v in coeff]
        tau=coeff[i]
        if tau<=0:continue
        other=coeff.copy();other[i]=0
        minimum,minflow=g.minimize(0,other,cl[2]);negative_maximum,maxflow=g.minimize(0,[-v for v in other],cl[2])
        maximum=-negative_maximum
        real_lower=F(-E-C-maximum,tau);real_upper=F(E-C-minimum,tau)
        newlo=max(state[0][i],real_lower.numerator//real_lower.denominator)
        newhi=min(state[1][i],ceil(real_upper))
        if newlo>state[0][i] or newhi<state[1][i]:
            lower[i]=newlo;upper[i]=newhi
            certificates.append({'coordinate':i,'direction':direction,'constant':str(C),'error':str(E),'coefficient':list(map(str,coeff)),
              'other_minimum':str(minimum),'other_maximum':str(maximum),'minimum_flow':minflow,'maximum_flow':maxflow,
              'lower_rational':str(real_lower),'upper_rational':str(real_upper),'new_lower':newlo,'new_upper':newhi,
              'scalar_affine_data':[[P,str(m0),str(m1),str(err),kind] for P,m0,m1,err,kind in data]})
    if not certificates:return state,[]
    if any(l>u for l,u in zip(lower,upper)):return None,certificates
    closed=g.close(lower,upper)
    if closed is None:return None,certificates
    return closed[:2],certificates

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'cover-correlated-direction.input.json.gz')
    ap.add_argument('--oracle',type=Path,default=HERE/'cover_newjet.json');ap.add_argument('--sample',type=int,default=1000)
    ap.add_argument('--iterations',type=int,default=4);ap.add_argument('--output',type=Path,default=HERE/'cover-newton-contractor.json')
    args=ap.parse_args();start=time.monotonic();raw=gzip.decompress(args.input.read_bytes());doc=json.loads(raw)
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
    oracle=api.make_correlated_oracle(args.oracle);rows=[];counts={'sample':len(states),'already_excluded':0,'contracted':0,'newly_excluded':0,'empty_after_contraction':0,'steps':0}
    for n,(p,original) in enumerate(sorted(states.items()),1):
        if engine.baseline.exclusion(original,True) or api.correlated_exclusion(original,oracle):counts['already_excluded']+=1;continue
        state=original;steps=[];excluded=None
        for k in range(args.iterations):
            new,certs=contract_once(state,oracle)
            if not certs:break
            steps.append({'old_cell':state,'new_cell':new,'certificates':certs});state=new;counts['steps']+=1
            if state is None:counts['empty_after_contraction']+=1;break
            excluded=api.correlated_exclusion(state,oracle)
            if excluded:counts['newly_excluded']+=1;break
        if steps:
            counts['contracted']+=1
            ratio=None if state is None else math.prod((state[1][i]-state[0][i]+1)/(original[1][i]-original[0][i]+1) for i in range(9))
            rows.append({'path':p,'iterations':len(steps),'final_box_volume_ratio_hint':ratio,'excluded':excluded,'steps':steps})
        if n%50==0:print(json.dumps({**counts,'done':n,'seconds':time.monotonic()-start}),flush=True)
    receipt={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),'snapshot_sha256':hashlib.sha256(args.input.read_bytes()).hexdigest(),
      'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'api_sources':api.api_sources(oracle),'counts':counts,
      'KKT_contraction_Lean_proven':False,'complete_global_minimizer_cover':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps({'receipt':receipt,'contractions':rows},separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
