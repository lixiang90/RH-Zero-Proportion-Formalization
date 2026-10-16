"""Uniform negative-curvature certificates excluding interior KKT minima.

Only directions supported on coordinates strictly above sep are used.
At a true global minimum their first derivative is zero and their second
derivative must be nonnegative. Upper interval Hessians select an integer
direction, then an exact integer quadratic upper bound is replayed.
The actual second-derivative and second-order-minimum Lean bridges are
explicit obligations; this script proves no zero-counting statement.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import argparse,functools,gzip,hashlib,json,time
import numpy as np
import cover_correlated_direction as engine
g=engine.g;w=engine.w;DS=engine.DS;HERE=Path(__file__).parent

class SecondOracle:
    def __init__(self,oracle):
        self.oracle=oracle;self.grid=[];self.step=oracle.step;self.width=g.SC//self.step
        for k in range(32*self.step):
            n=round(F(2*k+1,2*self.step));x=engine.I(F(k,self.step)-n,F(k+1,self.step)-n)
            value=oracle.poly(n,x,1);rem=F(44,7)**24*F(1,2)**22/factorial(22)
            self.grid.append([engine.floor((value.l-rem)*DS) if hasattr(engine,'floor') else ((value.l-rem)*DS).numerator//((value.l-rem)*DS).denominator,engine.ceil((value.u+rem)*DS)])
        self.levels=[self.grid]
        while len(self.levels[-1])>1:
            old=self.levels[-1];self.levels.append([[min(old[k][0],old[k+1][0]),max(old[k][1],old[k+1][1])] for k in range(0,len(old),2)])
    @functools.lru_cache(200000)
    def query(self,l,u):
        if l<0 or u>32*g.SC:return -40*DS,40*DS
        left=l//self.width;right=(max(l+1,u)+self.width-1)//self.width;low=10**100;up=-10**100;level=0
        while left<right:
            if left&1:low=min(low,self.levels[level][left][0]);up=max(up,self.levels[level][left][1]);left+=1
            if right&1:right-=1;low=min(low,self.levels[level][right][0]);up=max(up,self.levels[level][right][1])
            left//=2;right//=2;level+=1
        return low,up

def exclusion(state,oracle):
    free=[i for i in range(9) if state[0][i]>g.SEP]
    if not free:return None
    intervals=[oracle.query(state[0][g.LOOK[i,j]],state[1][g.LOOK[i,j]]) for i,j,a in g.TERMS]
    H=np.zeros((9,9))
    for (i,j,a),(l,u) in zip(g.TERMS,intervals):H[i:j,i:j]+=(a/g.D)*(u/DS)
    values,vectors=np.linalg.eigh(H[np.ix_(free,free)])
    for column,eigenvalue in enumerate(values):
        if eigenvalue>=-1e-10:break
        real=vectors[:,column];scale=max(abs(v) for v in real)
        for den in [1,16,256,65536]:
            d=[0]*9
            for k,i in enumerate(free):d[i]=round(real[k]/scale*den)
            upper=sum(a*sum(d[i:j])**2*u for (i,j,a),(l,u) in zip(g.TERMS,intervals))
            if upper<0:return {'kind':'negative_curvature','direction':d,'direction_scale':den,'second_upper_numerator':str(upper),
              'denominator':str(g.D*DS),'eigenvalue_hint':float(eigenvalue),'strictly_interior_support':free}
    return None

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'cover-correlated-direction.input.json.gz')
    ap.add_argument('--max-nodes',type=int,default=10000);ap.add_argument('--output',type=Path,default=HERE/'cover-second-order.json')
    args=ap.parse_args();start=time.monotonic();raw=gzip.decompress(args.input.read_bytes());doc=json.loads(raw);branches={r['path']:r for r in doc['branches']}
    original=json.loads((HERE/'cover-correlated-direction.json').read_bytes());assert original['receipt']['input_sha256']==hashlib.sha256(raw).hexdigest()
    oldextra={r['path'] for r in original['exclusions']};first=engine.TaylorOracle(HERE/'cover_newjet.json');oracle=SecondOracle(first)
    todo=[(w.root(),'r')];rows=[];checked=0;newcount=0
    while todo and checked<args.max_nodes:
        state,path=todo.pop();checked+=1;result=exclusion(state,oracle)
        if result:
            old=path in oldextra or engine.baseline.exclusion(state,True) is not None
            if not old:newcount+=1
            rows.append({'path':path,'new_over_first_order':not old,'result':result})
        if path in branches:
            r=branches[path]
            for bit,upper in [('1',False),('0',True)]:
                child=g.split(state,r['axis'],r['cut'],upper)
                if child is not None:todo.append((child,path+bit))
        if checked%1000==0:print(json.dumps({'checked':checked,'negative_curvature':len(rows),'new_over_first_order':newcount,'seconds':time.monotonic()-start}),flush=True)
    top=[]
    for row in sorted((r for r in rows if r['new_over_first_order']),key=lambda r:(len(r['path']),r['path'])):
        if not any(row['path'].startswith(t['path']) for t in top):top.append(row)
    covered=sum(any(p.startswith(r['path']) for r in top) for p in branches)
    receipt={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'Taylor_table_sha256':first.sha,'checked':checked,'negative_curvature_cells':len(rows),'new_over_first_order':newcount,
      'topmost_new_cells':len(top),'old_branches_covered_by_new_cells':covered,'second_order_Lean_bridges_complete':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps({'receipt':receipt,'exclusions':rows},separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
