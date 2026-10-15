"""Exact compatibility experiment using inherited leaf lower bounds.

This exploratory replay is not a Lean certificate or a new zero bound.
"""
from pathlib import Path
import importlib.util, json, argparse, time
import numpy as np

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('finite_source',ROOT/'scripts/finite_margin_20261015.py')
f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
SCALE=10**20;SC=32768

def collect(limit):
    leaves=[]
    def walk(walker,s,pos=1):
        w=walker.bits(pos)
        if w&1:
            ax=(w>>1)&63;md=(w>>7)&1;i,j=f.ALL[ax]
            q=f.bcut(s[0][ax],s[1][ax]) if md else (s[0][ax]+s[1][ax])>>1
            pp=walk(walker,f.split(s,i,j,q,True),pos+8)
            return walk(walker,f.split(s,i,j,q,False),pp)
        if s[1][7]<s[0][0]:return pos+1
        assert not (w>>1)&1
        margin,o=f.calc(s,w>>2)
        num=margin+f.CN*f.SLOPE
        if num<limit*f.SLOPE:
            leaves.append({'root':walker.n,'pos':pos,'lo':s[0],'hi':s[1],'value_num':num})
        return pos+2+o
    for r,(idx,end) in f.rootrecords.items():
        assert walk(f.Walker(r),f.root(idx))==end
    reflected=[]
    for leaf in leaves:
        reflected.append({**leaf,'reflected':True,
            'lo':[leaf['lo'][f.LOOK[8-j,8-i]] for i,j in f.ALL],
            'hi':[leaf['hi'][f.LOOK[8-j,8-i]] for i,j in f.ALL]})
    return leaves+reflected

def closure(a,b):
    d=np.full((10,10),10**9,dtype=np.int64);np.fill_diagonal(d,0)
    for shift,cell in [(0,a),(1,b)]:
        for (i,j),lo,hi in zip(f.ALL,cell['lo'],cell['hi']):
            i+=shift;j+=shift;d[i,j]=min(d[i,j],hi);d[j,i]=min(d[j,i],-lo)
    for k in range(10):
        d=np.minimum(d,d[:,k,None]+d[None,k,:])
    if np.any(np.diag(d)<0):return None
    return int(-d[9,0]),int(d[0,9])

def main():
    p=argparse.ArgumentParser();p.add_argument('--increment',type=int,default=5*10**13)
    args=p.parse_args();start=time.monotonic();target=f.NEW_CN+args.increment
    leaves=collect(f.NEW_CN+2*args.increment)
    covers=f.cover_thresholds();assert min(x[-1] for x in covers)>=f.NEW_CN+2*args.increment
    print(json.dumps({'low_leaves':len(leaves),'pairs_before_filter':len(leaves)**2}),flush=True)
    failures=[];compatible=negative=filtered=0;best=None
    for i,a in enumerate(leaves):
        for j,b in enumerate(leaves):
            if a['value_num']+b['value_num']>=2*target*f.SLOPE:continue
            if any(max(a['lo'][r+1],b['lo'][r])>min(a['hi'][r+1],b['hi'][r]) for r in range(7)):
                filtered+=1;continue
            cl=closure(a,b)
            if cl is None:negative+=1;continue
            compatible+=1;lo,hi=cl;wl=f.lb(lo,hi)
            floor_num=a['value_num']+b['value_num']+4*wl*f.SLOPE*10**7
            # Twice F10 = F9(left)+F9(right)+4*w(long span).
            if best is None or floor_num<best[0]:best=(floor_num,i,j,lo,hi,wl)
            if floor_num<2*target*f.SLOPE:
                failures.append({'left':i,'right':j,'lo_long':lo,'hi_long':hi,'w_lower':wl,
                    'candidate_floor':floor_num/(2*f.SLOPE*SCALE)})
    result={'scope':'exact inherited-leaf exploration; not Lean verified',
        'target_cN':str(target),'increment':str(args.increment),'low_leaves':len(leaves),
        'gap_filtered':filtered,'closure_infeasible':negative,'compatible_low_pairs':compatible,
        'unresolved_pairs':len(failures),'failures_first_50':failures[:50],
        'best_lower':None if best is None else best[0]/(2*f.SLOPE*SCALE),
        'best_detail':best,'elapsed_seconds':time.monotonic()-start}
    out=Path(__file__).with_name('overlap-leaf-graph.json')
    out.write_text(json.dumps({'summary':result,'leaves':leaves,'failures':failures},indent=2)+'\n',encoding='utf8')
    print(json.dumps(result),flush=True)

if __name__=='__main__':main()
