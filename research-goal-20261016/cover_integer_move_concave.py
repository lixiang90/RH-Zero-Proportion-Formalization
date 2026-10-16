"""One-sided cross-well comparison using signed finite-difference curvature.

If h_s'' <= B on the scalar interval, its tangent plus max(B,0)*r^2/2
is an upper bound. Negative curvature of the difference is retained: a
concave difference needs no quadratic remainder payment. This is a global
competitor test, with separate sublevel and KKT refinements when requested.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import argparse,functools,hashlib,json,time
import cover_integer_move as base
import cover_sublevel_obbt_api as obbt
import window_lower_global_cover as low

g=base.g;DS=base.DS;I=base.I;ceil=base.ceil;HERE=Path(__file__).parent

class ConcaveDifferenceOracle(base.DifferenceOracle):
    def install(self,shift):
        assert 1<=shift<=31
        if shift in self.tables:return
        cs={n:[I(y.l-x.u,y.u-x.l) for x,y in zip(self.taylor.coeff[n],self.taylor.coeff[n+shift])] for n in range(33-shift)}
        rem=2*base.first.M24*F(1,2)**22/factorial(22);grid=[]
        for k in range((32-shift)*self.taylor.step):
            n=round(F(2*k+1,2*self.taylor.step));x=I(F(k,self.taylor.step)-n,F(k+1,self.taylor.step)-n);v=I(0)
            for j in range(len(cs[n])-1,0,-1):v=v*x+cs[n][j]*j
            lower=(v.l-rem)*DS
            grid.append([lower.numerator//lower.denominator,ceil((v.u+rem)*DS)])
        while len(grid)&(len(grid)-1):grid.append([0,0])
        levels=[grid]
        while len(levels[-1])>1:
            old=levels[-1];levels.append([[min(old[k][0],old[k+1][0]),max(old[k][1],old[k+1][1])] for k in range(0,len(old),2)])
        self.tables[shift]=levels
    @functools.lru_cache(200000)
    def second_range(self,l,u,shift):
        if shift<0:
            lower,upper=self.second_range(l+shift*g.SC,u+shift*g.SC,-shift)
            return -upper,-lower
        assert shift>0 and l>=0 and u+shift*g.SC<=32*g.SC
        self.install(shift);levels=self.tables[shift]
        left=l//self.width;right=(max(l+1,u)+self.width-1)//self.width;lower=10**100;upper=-10**100;level=0
        while left<right:
            if left&1:lower=min(lower,levels[level][left][0]);upper=max(upper,levels[level][left][1]);left+=1
            if right&1:right-=1;lower=min(lower,levels[level][right][0]);upper=max(upper,levels[level][right][1])
            left//=2;right//=2;level+=1
        return lower,upper
    @functools.lru_cache(200000)
    def affine(self,l,u,shift):
        if min(l,l+shift*g.SC)<0 or max(u,u+shift*g.SC)>32*g.SC:return None
        P=l+u;radius=F(u-l,2*g.SC);v,s=self.point(P,shift)
        m0=round((v.l+v.u)*DS/2);m1=round((s.l+s.u)*DS/2)
        e0=max(abs(v.l*DS-m0),abs(v.u*DS-m0));e1=max(abs(s.l*DS-m1),abs(s.u*DS-m1))
        B=max(0,self.second_range(l,u,shift)[1])
        return P,m0,m1,ceil(e0+e1*radius+F(B)*radius**2/2)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'cover-sublevel-obbt.json')
    ap.add_argument('--frontier',action='store_true');ap.add_argument('--obbt',action='store_true')
    ap.add_argument('--newton-rounds',type=int,default=8);ap.add_argument('--max-cells',type=int,default=300)
    ap.add_argument('--moves',type=int,default=8);ap.add_argument('--output',type=Path,default=HERE/'cover-integer-move-concave.json')
    args=ap.parse_args();start=time.monotonic();raw=args.input.read_bytes();doc=json.loads(raw)
    taylor=base.api.make_correlated_oracle();oracle=ConcaveDifferenceOracle(taylor);engine=obbt.make_engine(low) if args.obbt else None
    target=low.g.TARGET if args.frontier else int(doc['receipt']['target_numerator'])
    counts={'checked_cells':0,'extra_OBBT_paths':0,'extra_OBBT_bounds':0,'Newton_paths':0,'already_closed':0,
      'cells_with_improving_midpoint_move':0,'minimum_midpoint_move_hint':0.,'strict_integer_move_exclusions':0};rows=[]
    inputs=doc['frontier'] if args.frontier else [r for r in doc['contractions'] if r['result'] is None and r['new_cell'] is not None]
    for original in inputs[:args.max_cells]:
        counts['checked_cells']+=1;state=original['state'] if args.frontier else original['new_cell'];state=(state[0],state[1]);steps=[];extra=None
        if args.obbt:
            rec=base.w.certify(state);axis,_=g.cut(state,rec);refined,bounds=obbt.contract(state,target,sorted(set(list(range(9))+[axis])),engine)
            if bounds:
                counts['extra_OBBT_paths']+=1;counts['extra_OBBT_bounds']+=len(bounds)
                extra={'old_cell':state,'new_cell':refined,'certificates':bounds};state=refined
            if state is None:counts['already_closed']+=1;continue
        if args.newton_rounds:
            state,steps,ex=base.newton.contract(state,args.newton_rounds,taylor)
            if steps:counts['Newton_paths']+=1
            if state is None or ex:counts['already_closed']+=1;continue
        if base.first.baseline.exclusion(state,True) or base.api.correlated_exclusion(state,taylor):counts['already_closed']+=1;continue
        rec=base.w.certify(state)
        if int(rec.get('floor_numerator','-1'))>=target:counts['already_closed']+=1;continue
        result=base.exclusion(state,oracle,args.moves,counts)
        if result:
            result['scalar_recipe']='signed-difference-upper-v1';counts['strict_integer_move_exclusions']+=1
            rows.append({'path':original['path'],'cell':state,'extra_sublevel_step':extra,'newton_steps':steps,'result':result})
        if counts['checked_cells']%25==0:print(json.dumps({**counts,'seconds':time.monotonic()-start}),flush=True)
    receipt={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),'input_kind':'frontier' if args.frontier else 'OBBT_residual',
      'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'base_source_sha256':hashlib.sha256(Path(base.__file__).read_bytes()).hexdigest(),
      'table_sha256':taylor.sha,'target_numerator':str(target),'newton_rounds':args.newton_rounds,'obbt_applied':args.obbt,
      'counts':counts,'move_limit':args.moves,'complete_global_cover':False,'actual_difference_analytic_Lean_bridge_complete':False,
      'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps({'receipt':receipt,'exclusions':rows},separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
