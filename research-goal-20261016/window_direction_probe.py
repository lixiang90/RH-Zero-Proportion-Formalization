"""Exact feasible KKT directions that cancel common long-span derivatives.

Tests e_i-e_j before optional convex LP discovery. LP is heuristic only:
every retained direction is rationalized and its strict upper derivative
bound recomputed with integers. The coercive-minimum and derivative bridges
are separate Lean obligations. No lower bound is asserted by this probe.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse, functools, hashlib, json, math, sys, time
import numpy as np
from scipy.optimize import linprog
import window_global_cover as w
g=w.g;HERE=Path(__file__).resolve().parent

def install_grid(path):
    raw=path.read_bytes();doc=json.loads(raw);receipt=doc['receipt']
    assert receipt['parameter_sha256']==hashlib.sha256(w.PARAM.read_bytes()).hexdigest()
    grid=doc['ranges'];step=receipt['grid_step'];maximum=receipt['maximum'];ds=receipt['denominator']
    assert len(grid)==step*maximum and g.SC%step==0 and maximum==32
    levels=[grid]
    while len(levels[-1])>1:
        old=levels[-1];assert len(old)%2==0
        levels.append([[min(old[k][0],old[k+1][0]),max(old[k][1],old[k+1][1])] for k in range(0,len(old),2)])
    @functools.lru_cache(200000)
    def query(l,u):
        if l<0 or u>maximum*g.SC:return -7*ds,7*ds
        width=g.SC//step;left=l//width;right=(max(l+1,u)+width-1)//width
        dl=10**100;du=-10**100;level=0
        while left<right:
            if left&1:dl=min(dl,levels[level][left][0]);du=max(du,levels[level][left][1]);left+=1
            if right&1:right-=1;dl=min(dl,levels[level][right][0]);du=max(du,levels[level][right][1])
            left//=2;right//=2;level+=1
        return dl,du
    w.derivative_range=query;w.DS=ds
    return hashlib.sha256(raw).hexdigest()

def ranges(state):
    return [w.derivative_range(state[0][g.LOOK[i,j]],state[1][g.LOOK[i,j]]) for i,j,a in g.TERMS]

def upper(direction,dr):
    value=sum(b*d*w.DS for b,d in zip(g.BS,direction))
    for (i,j,a),(l,u) in zip(g.TERMS,dr):
        s=sum(direction[i:j]);value+=a*s*(u if s>=0 else l)
    return value

def exclusion(state,use_lp=False):
    dr=ranges(state)
    best=None
    for i in range(9):
        for j in range(9):
            if i==j or state[0][j]<=g.SEP:continue
            direction=[int(r==i)-int(r==j) for r in range(9)]
            v=upper(direction,dr)
            if v<0 and (best is None or v<int(best['upper_numerator'])):
                best={'direction':direction,'upper_numerator':str(v),'denominator':str(g.D*w.DS),'kind':'two_coordinate'}
    if best is not None or not use_lp:return best
    rows=[];rhs=[]
    for t,((i,j,a),(l,u)) in enumerate(zip(g.TERMS,dr)):
        for value in [l/w.DS,u/w.DS]:
            row=np.zeros(9+len(g.TERMS));row[i:j]=value;row[9+t]=-1
            rows.append(row);rhs.append(0)
    obj=np.r_[np.array(g.BS)/g.D,[a/g.D for i,j,a in g.TERMS]]
    bounds=[(0 if state[0][i]<=g.SEP else -1,1) for i in range(9)]+[(None,None)]*len(g.TERMS)
    lp=linprog(obj,A_ub=rows,b_ub=rhs,bounds=bounds,method='highs')
    if not lp.success or lp.fun>=-1e-10:return None
    for den in [1,16,256,65536]:
        direction=[round(float(v)*den) for v in lp.x[:9]]
        assert all(v>=0 or state[0][i]>g.SEP for i,v in enumerate(direction))
        v=upper(direction,dr)
        if v<0:return {'direction':direction,'upper_numerator':str(v),'denominator':str(g.D*w.DS),
                       'kind':'rationalized_LP','direction_scale':den}
    return None

def main():
    ap=argparse.ArgumentParser();ap.add_argument('input',type=Path)
    ap.add_argument('--max-nodes',type=int,default=10000);ap.add_argument('--lp',action='store_true')
    ap.add_argument('--oracle',type=Path)
    ap.add_argument('--output',type=Path,default=HERE/'window-direction-probe.json');args=ap.parse_args()
    oracle_sha=install_grid(args.oracle) if args.oracle else None
    raw=args.input.read_bytes();data=json.loads(raw);branches={x['path']:x for x in data['branches']}
    leaves={x['path']:x for x in data['accepted']};front={x['path']:x for x in data['unresolved']}
    todo=[(w.root(),'r')];start=time.monotonic();excluded=[];checked=0
    while todo and checked<args.max_nodes:
        state,path=todo.pop();checked+=1
        result=exclusion(state,args.lp)
        if result:excluded.append({'path':path,'result':result})
        if path in branches:
            b=branches[path]
            for suffix,up in [('1',False),('0',True)]:
                child=g.split(state,b['axis'],b['cut'],up)
                if child is not None:todo.append((child,path+suffix))
        if checked%500==0:print(json.dumps({'checked':checked,'excluded':len(excluded),'seconds':time.monotonic()-start}),flush=True)
    tops=[]
    for row in sorted(excluded,key=lambda x:(len(x['path']),x['path'])):
        if not any(row['path'].startswith(x['path']) for x in tops):tops.append(row)
    saved=sum(any(path.startswith(x['path']) for x in tops) for path in branches)
    out={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),
         'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         'oracle_sha256':hashlib.sha256(Path(w.__file__).read_bytes()).hexdigest(),
         'derivative_grid_sha256':oracle_sha,
         'checked_nodes':checked,'exclusions':excluded,'topmost_exclusions':tops,
         'covered_old_branches':saved,'seconds':time.monotonic()-start,
         'global_floor_Lean_proven':False,'new_zero_proportion_proven':False}
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:out[k] for k in ['checked_nodes','covered_old_branches','seconds']}),flush=True)

if __name__=='__main__':main()
