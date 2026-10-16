"""Correlated directional derivative certificates for the new 24-mode window.

Each w'(span) is enclosed by affine Taylor data plus an explicit remainder.
All affine parts share the same nine gaps and are optimized jointly over the
complete difference-constraint cell. Floating LP selects a direction, then
exact integer min-cost flow certifies its strict negative upper derivative.
The final generic minimizer, jet and profile analytic bridges are separate
Lean obligations. No pointwise energy floor is claimed here.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import argparse, functools, gzip, hashlib, json, time
import numpy as np
from scipy.optimize import linprog
import window_direction_probe as baseline
w=baseline.w;g=w.g;I=w.ik.I;HERE=Path(__file__).parent
DS=10**15;M24=F(44,7)**24

def ceil(x):return -((-x.numerator)//x.denominator)

class TaylorOracle:
    def __init__(self,path):
        doc=json.loads(path.read_bytes());self.receipt=doc['receipt'];self.sha=hashlib.sha256(path.read_bytes()).hexdigest()
        assert self.receipt['parameter_sha256']==hashlib.sha256(w.PARAM.read_bytes()).hexdigest()
        self.coeff={int(n):[I(F(l),F(u)) for l,u in cs] for n,cs in doc['integer_taylor_coefficients'].items()}
        self.step=self.receipt['grid_step'];self.maximum=self.receipt['maximum']
        assert self.maximum==32 and self.receipt['order']==24
        self.third=[]
        for k in range(32*self.step):
            n=round(F(2*k+1,2*self.step));x=I(F(k,self.step)-n,F(k+1,self.step)-n)
            value=self.poly(n,x,2);rem=M24*F(1,2)**21/factorial(21)
            self.third.append(ceil(max(abs(value.l-rem),abs(value.u+rem))*DS))
        self.levels=[self.third]
        while len(self.levels[-1])>1:
            old=self.levels[-1];self.levels.append([max(old[k],old[k+1]) for k in range(0,len(old),2)])
        baseline.install_grid(path)
    def poly(self,n,x,derivative):
        cs=self.coeff[n];value=I(0)
        for j in range(len(cs)-1,derivative-1,-1):value=value*x+cs[j]*F(factorial(j),factorial(j-derivative))
        return value
    @functools.lru_cache(200000)
    def point(self,P):
        p=F(P,2*g.SC);n=round(p);x=p-n
        a=self.poly(n,I(x),0);b=self.poly(n,I(x),1)
        e1=M24*abs(x)**23/factorial(23);e2=M24*abs(x)**22/factorial(22)
        return I(a.l-e1,a.u+e1),I(b.l-e2,b.u+e2)
    @functools.lru_cache(200000)
    def third_bound(self,l,u):
        if l<0 or u>32*g.SC:return ceil(F(44,7)**3*DS)
        width=g.SC//self.step;left=l//width;right=(max(l+1,u)+width-1)//width;ans=0;level=0
        while left<right:
            if left&1:ans=max(ans,self.levels[level][left]);left+=1
            if right&1:right-=1;ans=max(ans,self.levels[level][right])
            left//=2;right//=2;level+=1
        return ans
    @functools.lru_cache(200000)
    def affine(self,l,u):
        dl,du=w.derivative_range(l,u);P=l+u;radius=F(u-l,2*g.SC)
        if u>32*g.SC or u-l>=2*g.SC:return P,(dl+du)//2,0,ceil(F(du-dl,2)),'interval'
        v,s=self.point(P);m0=round((v.l+v.u)*DS/2);m1=round((s.l+s.u)*DS/2)
        e0=max(abs(v.l*DS-m0),abs(v.u*DS-m0));e1=max(abs(s.l*DS-m1),abs(s.u*DS-m1))
        err=ceil(e0+e1*radius+F(self.third_bound(l,u))*radius**2/2)
        # Fall back on the exact interval bound when the curvature remainder
        # alone is worse. Retain a moderate affine-width loss because shared
        # gap correlations can still make the joint bound much tighter.
        if 2*err>du-dl:return P,(dl+du)//2,0,ceil(F(du-dl,2)),'interval'
        return P,m0,m1,err,'affine'

def select_direction(state,data):
    # Approximate feasible KKT gradients as b+H*g+A*epsilon. A positive
    # optimum of the L1 KKT residual provides a separating direction.
    terms=len(g.TERMS);variables=18+terms
    constant=np.array(g.BS,dtype=float)/g.D;H=np.zeros((9,9));E=np.zeros((9,terms))
    for t,((i,j,a),(P,m0,m1,err,kind)) in enumerate(zip(g.TERMS,data)):
        constant[i:j]+=(a/g.D)*(m0/DS-(m1/DS)*P/(2*g.SC))
        H[i:j,i:j]+=(a/g.D)*(m1/DS)
        E[i:j,t]=(a/g.D)*(err/DS)
    A=[];rhs=[]
    for z,(i,j) in enumerate(g.ALL):
        row=np.zeros(variables);row[i:j]=1;A.extend([row,-row]);rhs.extend([state[1][z]/g.SC,-state[0][z]/g.SC])
    indices=[]
    for i in range(9):
        if state[0][i]>g.SEP:
            row=np.r_[H[i],E[i],np.zeros(9)];row[9+terms+i]=-1;A.append(row);rhs.append(-constant[i]);plus=len(A)-1
        else:plus=None
        row=np.r_[-H[i],-E[i],np.zeros(9)];row[9+terms+i]=-1;A.append(row);rhs.append(constant[i]);minus=len(A)-1
        indices.append((plus,minus))
    obj=np.r_[np.zeros(9+terms),np.ones(9)];bounds=[(None,None)]*9+[(-1,1)]*terms+[(0,None)]*9
    lp=linprog(obj,A_ub=A,b_ub=rhs,bounds=bounds,method='highs')
    if not lp.success or lp.fun<1e-10:return None
    dual=lp.ineqlin.marginals
    d=[(0 if p is None else dual[p])-dual[m] for p,m in indices]
    assert all(v>=-1e-9 or state[0][i]>g.SEP for i,v in enumerate(d))
    return d,float(lp.fun)

def exact_upper(state,data,d):
    lo,hi=state
    assert all(v>=0 or lo[i]>g.SEP for i,v in enumerate(d))
    constant=2*g.SC*sum(b*DS*v for b,v in zip(g.BS,d));coeff=[0]*9;error=0
    for (i,j,a),(P,m0,m1,err,kind) in zip(g.TERMS,data):
        c=sum(d[i:j]);constant+=a*c*(2*g.SC*m0-m1*P);error+=2*g.SC*a*abs(c)*err
        for r in range(i,j):coeff[r]+=2*a*c*m1
    cl=g.close(*state);assert cl is not None and cl[:2]==state
    minusmax,flow=g.minimize(0,[-c for c in coeff],cl[2])
    value=constant+error-minusmax
    return value,{'constant':str(constant),'error':str(error),'coefficient':list(map(str,coeff)),
      'negative_maximum':str(minusmax),'flow':flow}

def exclusion(state,oracle):
    data=[oracle.affine(state[0][g.LOOK[i,j]],state[1][g.LOOK[i,j]]) for i,j,a in g.TERMS]
    hint=select_direction(state,data)
    if hint is None:return None
    reald,lpvalue=hint
    for den in [1,16,256,65536]:
        d=[round(v*den) for v in reald];num,flow=exact_upper(state,data,d)
        if num<0:return {'direction':d,'direction_scale':den,'upper_numerator':str(num),
            'denominator':str(2*g.SC*g.D*DS),'scalar_affine_data':[[P,str(m0),str(m1),str(err),kind] for P,m0,m1,err,kind in data],
            'affine_terms':sum(row[4]=='affine' for row in data),'exact_flow':flow,'lp_hint':lpvalue}
    return None

def main():
    ap=argparse.ArgumentParser();ap.add_argument('input',type=Path);ap.add_argument('--oracle',type=Path,default=HERE/'cover_newjet.json')
    ap.add_argument('--max-nodes',type=int,default=10000);ap.add_argument('--output',type=Path,default=HERE/'cover-correlated-direction.json')
    args=ap.parse_args();start=time.monotonic();raw=args.input.read_bytes();doc=json.loads(raw);branches={r['path']:r for r in doc['branches']}
    oracle=TaylorOracle(args.oracle);todo=[(w.root(),'r')];checked=0;rows=[];baselinecount=0
    while todo and checked<args.max_nodes:
        state,path=todo.pop();checked+=1
        old=baseline.exclusion(state,True)
        if old:baselinecount+=1
        else:
            result=exclusion(state,oracle)
            if result:rows.append({'path':path,'result':result})
        if path in branches:
            r=branches[path]
            for bit,upper in [('1',False),('0',True)]:
                child=g.split(state,r['axis'],r['cut'],upper)
                if child is not None:todo.append((child,path+bit))
        if checked%250==0:print(json.dumps({'checked':checked,'baseline':baselinecount,'additional':len(rows),'seconds':time.monotonic()-start}),flush=True)
    top=[]
    for row in sorted(rows,key=lambda r:(len(r['path']),r['path'])):
        if not any(row['path'].startswith(t['path']) for t in top):top.append(row)
    saved=sum(any(p.startswith(r['path']) for r in top) for p in branches)
    receipt={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),'oracle_sha256':oracle.sha,
      'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'baseline_helper_sha256':hashlib.sha256(Path(baseline.__file__).read_bytes()).hexdigest(),
      'checked':checked,'baseline_exact_descent_cells':baselinecount,'additional_correlated_descent_cells':len(rows),
      'additional_topmost':len(top),'additional_old_branches_covered':saved,'seconds':time.monotonic()-start,
      'actual_Taylor_and_KKT_Lean_bridges_complete':False,'unconditional_zero_proportion_proven':False}
    args.output.write_text(json.dumps({'receipt':receipt,'exclusions':rows},separators=(',',':'))+'\n',encoding='utf8')
    # Freeze the exact prefix used, since the active cover discovery evolves.
    snapshot=args.output.with_suffix('.input.json.gz');snapshot.write_bytes(gzip.compress(raw,mtime=0))
    print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
