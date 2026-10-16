"""Exclude global minima by strictly improving feasible integer-gap moves.

For delta in Z^9, compare F(g+delta)-F(g) on an entire cell. Each affected
span uses h_s(x)=w(x+s)-w(x). Same-phase Taylor coefficients are subtracted
before interval Horner evaluation, preserving the integer-shift correlation.
The nine gaps remain shared in the final exact flow maximum. A strict
decrease excludes global minima, including genuine nonglobal local minima.
Floating midpoint scores only select moves; acceptance is exact arithmetic.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import argparse,functools,hashlib,json,time
import numpy as np
import cover_correlated_direction as first
import cover_newwindow_gram as values
import cover_correlated_api as api
import cover_contractor_api as newton

g=first.g;w=first.w;DS=first.DS;I=first.I;ceil=first.ceil;HERE=Path(__file__).parent

class DifferenceOracle:
    def __init__(self,taylor):
        self.taylor=taylor;self.points=values.Points(json.loads((HERE/'cover_newjet.json').read_bytes()))
        self.width=g.SC//taylor.step;self.tables={};self.patterns=[r['integer_gaps'] for r in json.loads((HERE/'cover-newwindow-gram.json').read_bytes())['results']]
    @functools.lru_cache(200000)
    def point(self,P,shift):
        p=F(P,2*g.SC);v0,s0=self.points.at(p);v1,s1=self.points.at(p+shift)
        return I(v1.l-v0.u,v1.u-v0.l),I(s1.l-s0.u,s1.u-s0.l)
    def install(self,shift):
        assert 1<=shift<=31
        if shift in self.tables:return
        cs={n:[I(y.l-x.u,y.u-x.l) for x,y in zip(self.taylor.coeff[n],self.taylor.coeff[n+shift])]
          for n in range(33-shift)}
        rem=2*first.M24*F(1,2)**22/factorial(22);grid=[]
        for k in range((32-shift)*self.taylor.step):
            n=round(F(2*k+1,2*self.taylor.step));x=I(F(k,self.taylor.step)-n,F(k+1,self.taylor.step)-n);v=I(0)
            for j in range(len(cs[n])-1,0,-1):v=v*x+cs[n][j]*j
            grid.append(ceil(max(abs(v.l-rem),abs(v.u+rem))*DS))
        levels=[grid]
        # Pad to a power of two so dyadic range queries keep their indexing.
        while len(levels[0])&(len(levels[0])-1):levels[0].append(0)
        while len(levels[-1])>1:
            old=levels[-1];levels.append([max(old[k],old[k+1]) for k in range(0,len(old),2)])
        self.tables[shift]=levels
    @functools.lru_cache(200000)
    def second_bound(self,l,u,shift):
        if shift<0:return self.second_bound(l+shift*g.SC,u+shift*g.SC,-shift)
        assert shift>0 and l>=0 and u+shift*g.SC<=32*g.SC
        self.install(shift);levels=self.tables[shift]
        left=l//self.width;right=(max(l+1,u)+self.width-1)//self.width;ans=0;level=0
        while left<right:
            if left&1:ans=max(ans,levels[level][left]);left+=1
            if right&1:right-=1;ans=max(ans,levels[level][right])
            left//=2;right//=2;level+=1
        return ans
    @functools.lru_cache(200000)
    def affine(self,l,u,shift):
        assert shift!=0
        if min(l,l+shift*g.SC)<0 or max(u,u+shift*g.SC)>32*g.SC:return None
        P=l+u;radius=F(u-l,2*g.SC);v,s=self.point(P,shift)
        m0=round((v.l+v.u)*DS/2);m1=round((s.l+s.u)*DS/2)
        e0=max(abs(v.l*DS-m0),abs(v.u*DS-m0));e1=max(abs(s.l*DS-m1),abs(s.u*DS-m1))
        err=ceil(e0+e1*radius+F(self.second_bound(l,u,shift))*radius**2/2)
        return P,m0,m1,err

def candidates(state,oracle,limit):
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
    return [(hint,list(d)) for hint,d in scored if hint<-1e-10][:limit],(scored[0][0] if scored else None)

def exact_upper(state,delta,data):
    assert len(delta)==9 and any(delta) and all(state[0][k]+delta[k]*g.SC>=g.SEP for k in range(9))
    C=2*g.SC*DS*sum(b*d for b,d in zip(g.BS,delta));E=0;coeff=[0]*9
    for t,(P,m0,m1,err) in data:
        i,j,aw=g.TERMS[t];assert sum(delta[i:j])!=0
        C+=aw*(2*g.SC*m0-m1*P);E+=2*g.SC*aw*err
        for k in range(i,j):coeff[k]+=2*aw*m1
    closed=g.close(*state);assert closed is not None and closed[:2]==state
    minimum,flow=g.minimize(0,[-v for v in coeff],closed[2]);upper=C+E-minimum
    return upper,{'constant':str(C),'error':str(E),'coefficient':list(map(str,coeff)),'negative_maximum':str(minimum),'flow':flow}

def exclusion(state,oracle,limit=8,statistics=None):
    selected,best=candidates(state,oracle,limit)
    if statistics is not None:
        statistics['cells_with_improving_midpoint_move']+=int(bool(selected))
        if best is not None:statistics['minimum_midpoint_move_hint']=min(statistics['minimum_midpoint_move_hint'],best)
    for hint,delta in selected:
        data=[]
        for t,(i,j,aw) in enumerate(g.TERMS):
            shift=sum(delta[i:j])
            if not shift:continue
            z=g.LOOK[i,j];row=oracle.affine(state[0][z],state[1][z],shift)
            if row is None:break
            data.append((t,row))
        else:
            upper,flow=exact_upper(state,delta,data)
            if upper<0:return {'kind':'integer_move','delta':delta,'upper_numerator':str(upper),'denominator':str(2*g.SC*g.D*DS),
              'scalar_difference_data':[[t,P,str(m0),str(m1),str(err)] for t,(P,m0,m1,err) in data],
              'exact_flow':flow,'midpoint_difference_hint':hint}
    return None

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'cover-sublevel-obbt.json')
    ap.add_argument('--frontier',action='store_true');ap.add_argument('--newton-rounds',type=int,default=0)
    ap.add_argument('--max-cells',type=int,default=300);ap.add_argument('--moves',type=int,default=8)
    ap.add_argument('--output',type=Path,default=HERE/'cover-integer-move.json');args=ap.parse_args();start=time.monotonic()
    raw=args.input.read_bytes();doc=json.loads(raw);taylor=api.make_correlated_oracle();oracle=DifferenceOracle(taylor)
    rows=[];counts={'checked_cells':0,'Newton_paths':0,'Newton_direction_closed':0,'cells_with_improving_midpoint_move':0,
      'minimum_midpoint_move_hint':0.,'strict_integer_move_exclusions':0}
    inputs=doc['frontier'] if args.frontier else [r for r in doc['contractions'] if r['result'] is None and r['new_cell'] is not None]
    for original in inputs[:args.max_cells]:
        counts['checked_cells']+=1;state=original['state'] if args.frontier else original['new_cell'];state=(state[0],state[1]);steps=[]
        if args.newton_rounds:
            state,steps,ex=newton.contract(state,args.newton_rounds,taylor)
            if steps:counts['Newton_paths']+=1
            if state is None or ex:counts['Newton_direction_closed']+=1;continue
        result=exclusion(state,oracle,args.moves,counts)
        if result:
            counts['strict_integer_move_exclusions']+=1
            rows.append({'path':original['path'],'cell':state,'newton_steps':steps,'result':result})
        if counts['checked_cells']%25==0:print(json.dumps({**counts,'seconds':time.monotonic()-start}),flush=True)
    receipt={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),'input_kind':'frontier' if args.frontier else 'OBBT_residual',
      'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'table_sha256':taylor.sha,'api_sources':api.api_sources(taylor),
      'newton_rounds':args.newton_rounds,'move_limit':args.moves,'counts':counts,'complete_global_cover':False,
      'actual_difference_analytic_Lean_bridge_complete':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps({'receipt':receipt,'exclusions':rows},separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
