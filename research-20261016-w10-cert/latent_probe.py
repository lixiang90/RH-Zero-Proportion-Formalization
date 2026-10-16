"""Try reconstructing every scalar support from one nine-coordinate anchor.

The diagnostic uses numerical minimisation only to choose the anchor; every
reported accepted compression is replayed by exact integer mcheck arithmetic.
"""
from pathlib import Path
import argparse,bisect,json,time
import numpy as np
from scipy.optimize import linprog,minimize,LinearConstraint
import ordered_generate as o
import tree_flow as tree
import diagnose_frontier as diag
g=o.g;KEYS=[p for p,*_ in g.PT];POINT={p:(l,u) for p,l,u,*_ in g.PT};KEYS.sort()
INC=np.array([[int(i<=r<j) for r in range(9)] for i,j in g.ALL],float)

def supports(target,lo,hi,limit=0):
    out=[];skips=[]
    for i,j,a in g.TERMS:
        z=g.LOOK[i,j];l=lo[z];u=hi[z];x=sum(target[i:j])
        cut=bisect.bisect_right(KEYS,x);low=high=None;visits=[0,0]
        for side,indices in enumerate((range(cut-1,-1,-1),range(cut,len(KEYS)))):
            for n in indices:
                p=KEYS[n]
                if (side==0 and p<l) or (side==1 and p>u):break
                if limit and visits[side]>=limit:break
                visits[side]+=1;pl,pu=POINT[p]
                if l<=p<=u and pl<=l and u<=pu:
                    if side==0:low=p
                    else:high=p
                    break
        skips.append(visits)
        if low is None and high is None:out.append([0,0,0,0])
        elif low is None:out.append([1,0,high,0])
        elif high is None:out.append([1,0,low,0])
        elif low==high:out.append([1,0,low,0])
        else:
            m=min(1024,max(0,round((x-low)*1024/(high-low))))
            out.append([1,0,low,0] if not m else [1,0,high,0] if m==1024 else [3,m,low,high])
    return out,skips

def replay(fs,lo,hi):
    try:
        d=tree.recompute(fs,lo,hi);return int(d['after_numerator']),d['tree_code']
    except AssertionError as err:
        data=err.args[0]
        if isinstance(data,tuple) and data[0]=='Encoded dual failed':return data[2],data[1]
        raise

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=Path(__file__).with_name('ordered-0.json'))
    ap.add_argument('--output',type=Path,default=Path(__file__).with_name('latent-probe.json'));ap.add_argument('--limit',type=int,default=100)
    ap.add_argument('--lp-anchor',action='store_true');args=ap.parse_args()
    x=json.loads(args.input.read_text());rows=[z for z in x['accepted'] if 'FS' in z['result']]
    picked=[rows[i] for i in np.linspace(0,len(rows)-1,min(args.limit,len(rows)),dtype=int)]
    out=[];start=time.monotonic()
    for z in picked:
        r=z['result'];lo=r['certificate']['lower_bounds'];hi=r['certificate']['upper_bounds']
        ll=np.array(lo)/g.SC;uu=np.array(hi)/g.SC
        lp=linprog(np.zeros(9),A_ub=np.r_[INC,-INC],b_ub=np.r_[uu,-ll],bounds=[(None,None)]*9,method='highs');assert lp.success
        if args.lp_anchor:
            saved_target=g.TARGET
            try:
                g.TARGET=10**100
                cert=g.certify((lo,hi),False)
            finally:g.TARGET=saved_target
            position=np.array(cert['gaps']);fw=diag.fun(position)[0];success=True
        else:
            fit=minimize(diag.fun,lp.x,jac=True,method='SLSQP',constraints=[LinearConstraint(INC,ll,uu)],
                options={'ftol':1e-14,'maxiter':300});position=fit.x;fw=float(fit.fun);success=bool(fit.success)
        target=[min(u,max(l,int(round(v*g.SC)))) for v,l,u in zip(position,lo[:9],hi[:9])]
        fs,visits=supports(target,lo,hi);num,code=replay(fs,lo,hi)
        tests={}
        for budget in [4,8,16]:
            fs2,_=supports(target,lo,hi,budget)
            num2,code2=(num,code) if fs2==fs else replay(fs2,lo,hi)
            tests[str(budget)]={'passed':num2>=g.TARGET,'numerator':str(num2),'tree_code':code2}
        out.append({'path':z['path'],'target':target,'FS':fs,'tree_code':code,'numerator':str(num),
            'passed':num>=g.TARGET,'bounded_search':tests,'max_point_visits':max(max(v) for v in visits),
            'anchor_bits':sum((u-l).bit_length() for l,u in zip(lo[:9],hi[:9])),
            'actual_local_value':fw,'optimizer_success':success})
    stats={'scope':__doc__,'lp_anchor':args.lp_anchor,'processed':len(out),'passed':sum(r['passed'] for r in out),
        'bounded_passed':{str(n):sum(r['bounded_search'][str(n)]['passed'] for r in out) for n in [4,8,16]},
        'average_anchor_plus_tree_bits':sum(r['anchor_bits']+27 for r in out)/len(out),
        'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps({'stats':stats,'leaves':out},separators=(',',':'))+'\n');print(json.dumps(stats),flush=True)
if __name__=='__main__':main()
