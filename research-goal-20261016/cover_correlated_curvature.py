"""Correlated affine second variation on strict-interior directions.

Midpoint Hessian eigenvectors select integer directions only. Each w'' is
enclosed by its affine Taylor polynomial with w'''' remainder. Exact flow
maximizes the sum of all affine terms over the shared nine-gap cell. A
negative certified upper bound excludes an orthant global minimum.
Analytic jet connections and global completeness remain separate duties.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import argparse,functools,hashlib,json,time
import numpy as np
import cover_correlated_direction as first
import cover_second_order as second
import cover_contractor_api as newton

g=first.g;DS=first.DS;HERE=Path(__file__).parent;ceil=first.ceil

class CurvatureOracle:
    def __init__(self,taylor):
        self.taylor=taylor;self.interval=second.SecondOracle(taylor)
        self.width=g.SC//taylor.step;fourth=[]
        rem=first.M24*F(1,2)**20/factorial(20)
        for k in range(32*taylor.step):
            n=round(F(2*k+1,2*taylor.step));x=first.I(F(k,taylor.step)-n,F(k+1,taylor.step)-n)
            v=taylor.poly(n,x,3)
            fourth.append(ceil(max(abs(v.l-rem),abs(v.u+rem))*DS))
        self.levels=[fourth]
        while len(self.levels[-1])>1:
            old=self.levels[-1];self.levels.append([max(old[k],old[k+1]) for k in range(0,len(old),2)])
    @functools.lru_cache(200000)
    def fourth_bound(self,l,u):
        if l<0 or u>32*g.SC:return ceil(F(44,7)**4*DS)
        left=l//self.width;right=(max(l+1,u)+self.width-1)//self.width;ans=0;level=0
        while left<right:
            if left&1:ans=max(ans,self.levels[level][left]);left+=1
            if right&1:right-=1;ans=max(ans,self.levels[level][right])
            left//=2;right//=2;level+=1
        return ans
    @functools.lru_cache(200000)
    def point(self,P):
        p=F(P,2*g.SC);n=round(p);x=p-n
        v=self.taylor.poly(n,first.I(x),1);s=self.taylor.poly(n,first.I(x),2)
        ev=first.M24*abs(x)**22/factorial(22);es=first.M24*abs(x)**21/factorial(21)
        return first.I(v.l-ev,v.u+ev),first.I(s.l-es,s.u+es)
    @functools.lru_cache(200000)
    def affine(self,l,u):
        dl,du=self.interval.query(l,u);P=l+u
        if l<0 or u>32*g.SC or u-l>=2*g.SC:return P,(dl+du)//2,0,ceil(F(du-dl,2)),'interval'
        v,s=self.point(P);radius=F(u-l,2*g.SC)
        m0=round((v.l+v.u)*DS/2);m1=round((s.l+s.u)*DS/2)
        e0=max(abs(v.l*DS-m0),abs(v.u*DS-m0));e1=max(abs(s.l*DS-m1),abs(s.u*DS-m1))
        err=ceil(e0+e1*radius+F(self.fourth_bound(l,u))*radius**2/2)
        if 2*err>du-dl:return P,(dl+du)//2,0,ceil(F(du-dl,2)),'interval'
        return P,m0,m1,err,'affine'

def exact_upper(state,data,d):
    assert any(d) and all(v==0 or state[0][i]>g.SEP for i,v in enumerate(d))
    constant=error=0;coeff=[0]*9
    for (i,j,a),(P,m0,m1,err,kind) in zip(g.TERMS,data):
        c=sum(d[i:j]);q=a*c*c
        constant+=q*(2*g.SC*m0-m1*P);error+=2*g.SC*q*err
        for r in range(i,j):coeff[r]+=2*q*m1
    closed=g.close(*state);assert closed is not None and closed[:2]==state
    minimum,flow=g.minimize(0,[-v for v in coeff],closed[2])
    return constant+error-minimum,{'constant':str(constant),'error':str(error),'coefficient':list(map(str,coeff)),
      'negative_maximum':str(minimum),'flow':flow}

def exclusion(state,oracle,statistics=None):
    free=[i for i in range(9) if state[0][i]>g.SEP]
    if not free:return None
    data=[oracle.affine(state[0][g.LOOK[i,j]],state[1][g.LOOK[i,j]]) for i,j,a in g.TERMS]
    H=np.zeros((9,9))
    # A point Hessian selects a candidate even when interval upper matrices
    # have no negative eigenvalue. The exact flow below decides acceptance.
    for (i,j,a),(P,m0,m1,err,kind) in zip(g.TERMS,data):
        if kind=='affine':value=m0/DS
        elif P<=64*g.SC:
            v,_=oracle.point(P);value=float((v.l+v.u)/2)
        else:value=m0/DS
        H[i:j,i:j]+=(a/g.D)*value
    values,vectors=np.linalg.eigh(H[np.ix_(free,free)])
    if values[0]<-1e-10 and statistics is not None:statistics['negative_midpoint_Hessian']+=1
    seen=set()
    for col,eigenvalue in enumerate(values):
        if eigenvalue>=-1e-10:break
        v=vectors[:,col];scale=max(abs(v))
        for den in [1,16,256,65536]:
            d=[0]*9
            for k,i in enumerate(free):d[i]=round(v[k]/scale*den)
            if tuple(d) in seen:continue
            seen.add(tuple(d));upper,flow=exact_upper(state,data,d)
            if upper<0:return {'kind':'correlated_negative_curvature','direction':d,'direction_scale':den,
              'upper_numerator':str(upper),'denominator':str(2*g.SC*g.D*DS),'eigenvalue_hint':float(eigenvalue),
              'scalar_affine_data':[[P,str(m0),str(m1),str(err),kind] for P,m0,m1,err,kind in data],
              'exact_flow':flow,'affine_terms':sum(r[4]=='affine' for r in data)}
    return None

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'cover-sublevel-obbt.json')
    ap.add_argument('--newton-rounds',type=int,default=0);ap.add_argument('--max-cells',type=int,default=300)
    ap.add_argument('--output',type=Path,default=HERE/'cover-correlated-curvature.json');args=ap.parse_args();start=time.monotonic()
    raw=args.input.read_bytes();doc=json.loads(raw);taylor=first.TaylorOracle(HERE/'cover_newjet.json');oracle=CurvatureOracle(taylor)
    counts={'residual_OBBT_cells':0,'Newton_paths':0,'Newton_first_order_exclusions':0,'negative_midpoint_Hessian':0,
      'independent_interval_exclusions':0,'correlated_exclusions':0,'new_over_independent_interval':0};rows=[]
    for record in doc['contractions']:
        if record['result'] is not None or record['new_cell'] is None:continue
        if counts['residual_OBBT_cells']>=args.max_cells:break
        counts['residual_OBBT_cells']+=1;state=(record['new_cell'][0],record['new_cell'][1]);steps=[];ex=None
        if args.newton_rounds:
            state,steps,ex=newton.contract(state,args.newton_rounds,taylor)
            if steps:counts['Newton_paths']+=1
            if state is None or ex:counts['Newton_first_order_exclusions']+=1;continue
        old=second.exclusion(state,oracle.interval)
        if old:counts['independent_interval_exclusions']+=1
        result=exclusion(state,oracle,counts)
        if result:
            counts['correlated_exclusions']+=1
            if old is None:counts['new_over_independent_interval']+=1
            rows.append({'path':record['path'],'cell':state,'newton_steps':steps,'old_interval_exclusion':old,'result':result})
        if counts['residual_OBBT_cells']%25==0:print(json.dumps({**counts,'seconds':time.monotonic()-start}),flush=True)
    receipt={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'table_sha256':taylor.sha,'first_order_engine_sha256':hashlib.sha256(Path(first.__file__).read_bytes()).hexdigest(),
      'interval_second_order_engine_sha256':hashlib.sha256(Path(second.__file__).read_bytes()).hexdigest(),
      'newton_rounds':args.newton_rounds,'counts':counts,'complete_global_cover':False,'new_zero_proportion_proven':False,
      'actual_jet_Lean_bridge_complete':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps({'receipt':receipt,'exclusions':rows},separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
