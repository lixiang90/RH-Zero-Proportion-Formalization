"""Exact exploratory affine replay of inherited leaves with a new potential.

The old proof is unchanged.  Affine supports are extracted algebraically from
its mcheckP data; they have not yet been proved in Lean in this stronger form.
Each reported cell minimum is obtained by exact integer min-cost flow, retaining
all pair-distance constraints.  This is research evidence, not a new theorem.
"""
from pathlib import Path
import argparse, importlib.util, itertools, json, hashlib, time
import networkx as nx

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('finite_source', ROOT/'scripts/finite_margin_20261015.py')
f = importlib.util.module_from_spec(spec); spec.loader.exec_module(f)
DEN = f.SLOPE * 10**20
SC = 32768

def support(s, w):
    lo, hi = s; lower = lo[:8]; fs = []; off = 0
    for i,j,a,k in f.TS:
        ll,uu = f.term_bounds(s,i,j)
        dec,off = f.dec(w,off,ll,uu); fs.append(dec)
    pp,ss,cp,cm,off = f.ydec(w,off,s)
    mv=cn=cpadd=0; slopes=[0]*8; mass=[0]*8
    for (i,j,a,_),(k,m,p,r) in zip(f.TS,fs):
        ll,uu=f.term_bounds(s,i,j); uu=max(ll+1,uu); l0=sum(lower[i:j])
        l1,l2=f.weights(k,m)
        const=1024-l1-l2
        vp=f.PT.get(p,0); vr=f.PT.get(r,0)
        mv += a*(const*f.lb(ll,uu)+l1*(vp&f.MASK32)+l2*(vr&f.MASK32))
        sp=(vp>>32)&f.MASK32; sr=(vr>>32)&f.MASK32; dp=vp>>64; dr=vr>>64
        cn += a*(l1*f.nat(2000000000-dp)*f.nat(p-l0)+l2*f.nat(2000000000-dr)*f.nat(r-l0))
        cpadd += a*(l1*f.nat(dp-2000000000)*f.nat(p-l0)+l2*f.nat(dr-2000000000)*f.nat(r-l0))
        sl=a*(l1*sp+l2*sr); ma=a*(l1+l2)
        for rr in range(i,j): slopes[rr]+=sl; mass[rr]+=ma
    base=10240000000000*sum(b*l for b,l in zip(f.BS,lower))+32768*mv+10*(cpadd+cm-cn-cp)
    coeff=[10*(1024000000000*b+sl+ssr-2000000000*ma-pr)
           for b,sl,ssr,ma,pr in zip(f.BS,slopes,ss,mass,pp)]
    intercept=base-sum(c*l for c,l in zip(coeff,lower))
    floor=intercept+sum(c*(l if c>=0 else u) for c,l,u in zip(coeff,lower,hi[:8]))
    old,off2=f.calc(s,w)
    assert off==off2 and floor==old+f.CN*f.SLOPE
    return intercept,coeff,off

def collect():
    leaves=[]
    def walk(walker,s,pos=1):
        w=walker.bits(pos)
        if w&1:
            ax=(w>>1)&63;md=(w>>7)&1;i,j=f.ALL[ax]
            q=f.bcut(s[0][ax],s[1][ax]) if md else (s[0][ax]+s[1][ax])>>1
            end=walk(walker,f.split(s,i,j,q,True),pos+8)
            return walk(walker,f.split(s,i,j,q,False),end)
        if s[1][7]<s[0][0]:return pos+1
        if (w>>1)&1:
            raise AssertionError('Unexpected Farkas leaf; implement before using')
        intercept,coeff,off=support(s,w>>2)
        leaves.append({'root':walker.n,'pos':pos,'lo':s[0],'hi':s[1],
                       'intercept':intercept,'coeff':coeff,'reflected':False})
        return pos+2+off
    for r,(idx,end) in f.rootrecords.items():
        assert walk(f.Walker(r),f.root(idx))==end
    reflected=[]
    for cell in leaves:
        reflected.append({**cell,'reflected':True,'coeff':cell['coeff'][::-1],
            'lo':[cell['lo'][f.LOOK[8-j,8-i]] for i,j in f.ALL],
            'hi':[cell['hi'][f.LOOK[8-j,8-i]] for i,j in f.ALL]})
    return leaves+reflected

def potential():
    raw1=(Path(__file__).with_name('validate_affine_potential.json')).read_bytes()
    raw2=(Path(__file__).with_name('ternary_potential_oracle.json')).read_bytes()
    a=json.loads(raw1);b=json.loads(raw2)
    assert a['denominator']==b['rational_delta_denominator']==10**12
    assert a['centres_numerator']==[104,197] and a['centres_denominator']==100
    theta={int(k):v for k,v in a['potential_numerators'].items()}
    delta=b['rational_delta_numerators']; mu=[104,197]
    def psi(word):
        code=sum(t*3**i for i,t in enumerate(word))
        u=delta[code]*100;v=[0]*7
        if 2 not in word:
            code2=sum(t<<i for i,t in enumerate(word));row=theta.get(code2,[0]*8)
            u+=100*row[0]-sum(p*mu[t] for p,t in zip(row[1:],word))
            v=row[1:]
        return u,v # intercept /1e14, gap-slopes /1e12
    def difference(word):
        pu,pv=psi(word[:7]);qu,qv=psi(word[1:])
        const=(pu-qu)*(DEN//10**14)
        coeff=[x-y for x,y in zip(pv+[0],[0]+qv)]
        return const,[x*(DEN//(10**12*SC)) for x in coeff]
    return difference,{'binary_sha256':hashlib.sha256(raw1).hexdigest(),
                       'ternary_sha256':hashlib.sha256(raw2).hexdigest()}

def close(lo,hi):
    n=9; inf=10**20;d=[[0 if i==j else inf for j in range(n)] for i in range(n)]
    for (i,j),l,u in zip(f.ALL,lo,hi):d[i][j]=min(d[i][j],u);d[j][i]=min(d[j][i],-l)
    for k in range(n):
        for i in range(n):
            for j in range(n):d[i][j]=min(d[i][j],d[i][k]+d[k][j])
    if any(d[i][i]<0 for i in range(n)):return None
    return d

def minimize_exact(intercept, coeff, lo, hi, return_dual=False):
    d=close(lo,hi)
    if d is None:return None
    # Position coefficients c.  Flow divergence is c, so c.y >= -cost.
    c=[-coeff[0]]+[coeff[i-1]-coeff[i] for i in range(1,8)]+[coeff[7]]
    graph=nx.DiGraph()
    for i in range(9):graph.add_node(i,demand=-c[i])
    for i in range(9):
        for j in range(9):
            if i!=j:graph.add_edge(i,j,weight=d[i][j])
    cost,flow=nx.network_simplex(graph)
    # Explicit exact dual feasibility check; no floating-point LP is used.
    assert all(isinstance(v,int) and v>=0 for row in flow.values() for v in row.values())
    for i in range(9):
        incoming=sum(flow[j].get(i,0) for j in range(9))
        outgoing=sum(flow[i].values())
        assert incoming-outgoing==-c[i]
    assert cost==sum(v*d[i][j] for i,row in flow.items() for j,v in row.items())
    if return_dual:
        return intercept-cost,{'divergence':list(map(str,c)),
            'nonzero_flow':[[i,j,str(v),d[i][j]] for i,row in flow.items()
                            for j,v in row.items() if v],
            'cost':str(cost)}
    return intercept-cost

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--target',default='8598/1000000')
    ap.add_argument('--output',default='affine-leaf-replay.json');args=ap.parse_args()
    pn,pd=map(int,args.target.split('/'));assert DEN%pd==0
    target=pn*(DEN//pd);start=time.time();psi,hashes=potential();leaves=collect()
    # Work in q'=10*32768*g so sep=17/20 has an integer endpoint.
    bounds=[(278528,491520),(491520,819200),(819200,13107200)]
    minima=[];failures=[];count=empty=0
    for ix,cell in enumerate(leaves):
        choices=[[t for t,(l,u) in enumerate(bounds)
                  if max(10*cell['lo'][r],l)<=min(10*cell['hi'][r],u)] for r in range(8)]
        for word in itertools.product(*choices):
            lo=[10*x for x in cell['lo']];hi=[10*x for x in cell['hi']]
            for r,t in enumerate(word):lo[r]=max(lo[r],bounds[t][0]);hi[r]=min(hi[r],bounds[t][1])
            const,coeff=psi(word);coeff=[a+b for a,b in zip(cell['coeff'],coeff)]
            assert all(x%10==0 for x in coeff)
            val=minimize_exact(cell['intercept']+const,[x//10 for x in coeff],lo,hi)
            if val is None:empty+=1;continue
            count+=1;rec={'leaf':ix,'word':list(word),'value_numerator':str(val),
                         'floor':val/DEN,'root':cell['root'],'pos':cell['pos'],
                         'reflected':cell['reflected']}
            if val<target:failures.append(rec)
            minima.append(rec)
        if ix%1000==0:print(json.dumps({'leaves':ix,'cells':count,'failures':len(failures),
                                      'seconds':time.time()-start}),flush=True)
    result={'status':'exact affine arithmetic exploration, stronger support not yet formalized',
            'target':args.target,'input_hashes':hashes,'denominator':str(DEN),
            'leaf_count':len(leaves),'cell_count':count,'empty_cells':empty,
            'unresolved_count':len(failures),'minimum':min(minima,key=lambda r:r['floor']),
            'unresolved':failures,'elapsed_seconds':time.time()-start,
            'scope':'48 inherited roots only; good-gap complement requires a separate proof'}
    Path(__file__).with_name(args.output).write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in result.items() if k!='unresolved'}),flush=True)

if __name__=='__main__':main()
