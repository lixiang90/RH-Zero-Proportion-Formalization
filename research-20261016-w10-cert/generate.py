"""Exact-integer W10 cell certificate discovery; no floating lower bound is trusted.

Analytic supports are attributed to the frozen inherited PT/LB library. LP
duals only select convex weights; integer capacity checks and min-cost flow
produce each exported lower bound. A complete coverage tree still needs Lean.
"""
from pathlib import Path
import argparse, ast, functools, hashlib, importlib.util, json, math, os, re, time
import numpy as np
import networkx as nx
from scipy.optimize import linprog

ROOT=Path(__file__).resolve().parents[1]
SPEC=importlib.util.spec_from_file_location('inherited',ROOT/'scripts/finite_margin_20261015.py')
f=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(f)
PAR=ROOT/'research-20261016/spectral-w10-refined-rational.json'
P=json.loads(PAR.read_text());D=P['denominator'];SC=32768;LD=10**12;WD=10**10*SC;DEN=LD*WD
assert D==10**10 and LD%D==0
TERMS=[(i,j,a) for i,j,a in P['a_upper'] if a]
BS=P['b_numerators'];Q=9;N=10
ALL=[(i,i+1) for i in range(Q)]+[(i,j) for i in range(Q) for j in range(i+2,N)]
LOOK={p:i for i,p in enumerate(ALL)}
TARGET=433*(DEN//50000)
OLD=False
SEP=27852 # Outer approximation to 17/20, intentionally weaker.

def table():
    out=[]
    for j,ls in re.findall(r'\.lf (\d+) (\[[^\]]*\])',f.cert):
        for k,v in ast.literal_eval(ls):
            p=1024*int(j)+k;v3=v&((1<<96)-1)
            left=max(0,p-((v>>96)&((1<<20)-1)));right=p+(v>>116)
            sl=((v3>>32)&f.MASK32)-2000000000
            err=4000000000-((v3>>32)&f.MASK32)-(v3>>64)
            assert err>=0
            if right:out.append((p,left,right,v3&f.MASK32,sl,err))
    return out
PT=table()
KCOEF=np.array([1.,.012310798,-.015041681,.003867664,.006489926,-.000992327,.005580097,-.006846472,.003781297,-.005670353,.003355089,-.000450523,-.000218483])
KFREQ=np.r_[np.sqrt(2)/(2*np.pi),np.arange(1,13)]
KNORM=np.sinc(KFREQ)@KCOEF
def kernel(xs):
    return (((np.sinc(xs[:,None]+KFREQ)+np.sinc(xs[:,None]-KFREQ))@KCOEF)/(2*KNORM))**2

def close(lo,hi):
    d=[[0 if i==j else 10**15 for j in range(N)] for i in range(N)]
    for (i,j),l,u in zip(ALL,lo,hi):d[i][j]=u;d[j][i]=-l
    for k in range(N):
        dk=d[k]
        for i in range(N):
            ik=d[i][k];di=d[i]
            for j in range(N):
                v=ik+dk[j]
                if v<di[j]:di[j]=v
    if any(d[i][i]<0 for i in range(N)):return None
    return [-d[j][i] for i,j in ALL],[d[i][j] for i,j in ALL],d

def root():
    # b.q >= b_i*q_i + SEP*sum_{r!=i}b_r. This bounds each coordinate
    # whenever b.q < c*SC. Outward ceiling retains boundary points.
    cn=86600000 # target*D
    extra=cn*SC-sum(BS)*SEP
    up=[SEP+(extra+b-1)//b for b in BS]
    lo=[(j-i)*SEP for i,j in ALL];hi=[sum(up[i:j]) for i,j in ALL]
    # Optimize each span under positive pressure plus all other coordinates SEP.
    for z,(i,j) in enumerate(ALL):
        hi[z]=min(hi[z],(j-i)*SEP+(extra+min(BS[i:j])-1)//min(BS[i:j]))
    cl=close(lo,hi)
    assert cl is not None and cl[:2]==(lo,hi)
    return lo,hi

def split(s,ax,cut,upper):
    # Exact adaptation of the frozen PCell.cuB single-edge closure operation.
    lo,hi=s;i,j=ALL[ax];aa,bb,w=(i,j,cut) if upper else (j,i,-cut)
    def leg(a,b):return 0 if a==b else hi[LOOK[a,b]] if a<b else -lo[LOOK[b,a]]
    # Bounds here are tiny compared with Core's 2^42 offsets, so signed formula
    # agrees with its Nat-subtraction implementation on every nonempty cell.
    col=[leg(x,aa) for x in range(N)];row=[w+leg(bb,x) for x in range(N)]
    l=[max(v,-col[b]-row[a]) for v,(a,b) in zip(lo,ALL)]
    u=[min(v,col[a]+row[b]) for v,(a,b) in zip(hi,ALL)]
    if any(a>b for a,b in zip(l,u)):return None
    cl=close(l,u)
    assert cl is not None and cl[:2]==(l,u),('single-edge closure mismatch',ax,cut,upper)
    return l,u

@functools.lru_cache(200000)
def lines(l,u,base=None):
    ans=[(0,0,-2)]
    for p,pl,pu,v,sl,err in PT:
        if pl<=l and u<=pu and (not OLD or l<=p<=u):
            const=SC*v-10*sl*p-10*err*max(p-(base if OLD else l),0)
            ans.append((const,10*sl,p))
    lb=f.lb(l,max(l+1,u) if OLD else u)
    if lb:ans.append((SC*lb,0,-1))
    return ans

def minimize(intercept,coeff,d):
    div=[-coeff[0]]+[coeff[r-1]-coeff[r] for r in range(1,Q)]+[coeff[-1]]
    g=nx.DiGraph()
    for i in range(N):g.add_node(i,demand=-div[i])
    for i in range(N):
        for j in range(N):
            if i!=j:g.add_edge(i,j,weight=d[i][j])
    cost,flow=nx.network_simplex(g)
    nonzero=[[i,j,str(v),d[i][j]] for i,row in flow.items() for j,v in row.items() if v]
    chk=[0]*N
    for i,j,amount,u in nonzero:chk[i]+=int(amount);chk[j]-=int(amount)
    assert chk==div and cost==sum(int(v)*u for i,j,v,u in nonzero)
    return intercept-cost,{'divergence':list(map(str,div)),'nonzero_flow':nonzero,'cost':str(cost)}

def certify(s,export=False,pressure=False):
    if OLD and s[1][Q-1]<s[0][0]:return {'empty':True,'reflection':True}
    cl=close(*s)
    if cl is None:return {'empty':True}
    lo,hi,d=cl;meta=[];rows=[];rhs=[]
    assert (lo,hi)==tuple(s),'Unrecorded closure strengthening'
    if OLD:
        zero_total=10240000000000*sum(b*l for b,l in zip(BS,lo[:Q]))+SC*1024*sum(
            a*f.lb(lo[LOOK[i,j]],max(lo[LOOK[i,j]]+1,hi[LOOK[i,j]])) for i,j,a in TERMS)
        if zero_total>=TARGET:
            return {'floor_numerator':str(zero_total),'floor':zero_total/DEN,'fast_table':True,
                'mcheck_numerator':str(zero_total),'mcheck_floor':zero_total/DEN,
                'FS':[[0,0,0,0] for t in TERMS],
                'multiplier':{'P':['0']*Q,'S':['0']*Q,'Cp':'0','Cm':'0','steps':[]},
                'certificate':{'lower_bounds':lo,'upper_bounds':hi}}
    for t,(i,j,a) in enumerate(TERMS):
        z=LOOK[i,j]
        for const,slope,p in lines(lo[z],hi[z],sum(lo[i:j])):
            if p==-2:continue
            row=np.zeros(Q+len(TERMS));row[i:j]=slope/10**10;row[Q+t]=-1
            rows.append(row);rhs.append(-const/WD);meta.append((t,const,slope,p))
    for (i,j),l,u in zip(ALL,lo,hi):
        row=np.zeros(Q+len(TERMS));row[i:j]=1
        rows.extend([row,-row]);rhs.extend([u/SC,-l/SC])
    obj=np.r_[np.array(BS)/D,[a/D for i,j,a in TERMS]]
    if pressure:
        rows.append(np.r_[np.array(BS)/D,np.zeros(len(TERMS))]);rhs.append(.00866)
    lp=linprog(obj,A_ub=rows,b_ub=rhs,bounds=[(None,None)]*Q+[(0,None)]*len(TERMS),
        method='highs',options={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9})
    if not lp.success:
        if pressure:return certify(s,export,False)
        # Never accept infeasibility on a floating-only claim.
        return {'lp_failure':lp.message,'floor':-1,'gaps':lo[:Q]}
    mu=max(0.,-float(lp.ineqlin.marginals[-1])) if pressure else 0.
    lam=[int(math.floor(max(0,-x)*LD/(1+mu))) for x in lp.ineqlin.marginals[:len(meta)]]
    for t,(i,j,a) in enumerate(TERMS):
        ids=[k for k,m in enumerate(meta) if m[0]==t];mass=sum(lam[k] for k in ids);cap=a*(LD//D)
        if mass>cap:
            k=max(ids,key=lambda k:lam[k]);assert lam[k]>=mass-cap;lam[k]-=mass-cap
        assert sum(lam[k] for k in ids)<=cap
    fs=[]
    if OLD:
        quant=[0]*len(meta)
        for t,(i,j,a) in enumerate(TERMS):
            ids=[k for k,m in enumerate(meta) if m[0]==t and lam[k]]
            ids=sorted(ids,key=lambda k:lam[k],reverse=True)[:2]
            ids=[k for k in ids if meta[k][3]>=0]+[k for k in ids if meta[k][3]<0]
            if not ids:fs.append([0,0,0,0]);continue
            cap=a*(LD//D)
            if len(ids)==1 and meta[ids[0]][3]<0:
                quant[ids[0]]=a*1024;fs.append([0,0,0,0])
            elif len(ids)==1:
                k=ids[0];m=min(1024,max(0,round(lam[k]*1024/cap)))
                quant[k]=a*m;fs.append([1,0,meta[k][3],0] if m==1024 else [2,m,meta[k][3],0])
            elif meta[ids[1]][3]<0:
                k,k2=ids;m=min(1024,max(0,round(lam[k]*1024/cap)))
                quant[k]=a*m;quant[k2]=a*(1024-m);fs.append([2,m,meta[k][3],0])
            else:
                k,k2=ids;m=min(1024,max(0,round(lam[k2]*1024/cap)))
                quant[k]=a*(1024-m);quant[k2]=a*m;fs.append([3,m,meta[k][3],meta[k2][3]])
        lam=quant
    intercept=0;coeff=[b*(1024*10**10 if OLD else LD) for b in BS];mix=[]
    for weight,(t,const,slope,p) in zip(lam,meta):
        if not weight:continue
        i,j,a=TERMS[t];intercept+=weight*const
        for r in range(i,j):coeff[r]+=weight*slope
        mix.append([t,p,str(weight),str(const),str(slope)])
    if OLD:
        assert all(c%10==0 for c in coeff)
        ex10,fl10=minimize(0,[c//10 for c in coeff],d)
        exact=intercept+10*ex10;flow=fl10
    else:exact,flow=minimize(intercept,coeff,d)
    rec={'floor_numerator':str(exact),'floor':exact/DEN,'lp_floor':float(lp.fun),'gaps':lp.x[:Q].tolist(),
         'relaxation_values':lp.x[Q:].tolist(),'active_lines':len(mix),'constraint_count':len(rows)}
    if pressure:rec['pressure_multiplier']=mu
    if export:rec['certificate']={'lower_bounds':lo,'upper_bounds':hi,'mixture_denominator':LD,
        'mixture':mix,'intercept':str(intercept),'gap_coefficients':list(map(str,coeff)),'flow':flow}
    if OLD:
        rec['FS']=fs
        pp=[0]*Q;ss=[0]*Q;cp=cm=0;steps=[]
        for ii,jj,amount,u in flow['nonzero_flow']:
            y=int(amount);i=min(ii,jj);j=max(ii,jj)
            if j==i+1:continue
            adj=sum(lo[i:j]);upper=ii<jj;z=LOOK[i,j]
            if upper:
                for r in range(i,j):ss[r]+=y
                cp+=y*max(hi[z]-adj,0);cm+=y*max(adj-hi[z],0)
            else:
                for r in range(i,j):pp[r]+=y
                cp+=y*max(adj-lo[z],0);cm+=y*max(lo[z]-adj,0)
            steps.append([i,j,upper,str(y)])
        rec['multiplier']={'P':list(map(str,pp)),'S':list(map(str,ss)),'Cp':str(cp),'Cm':str(cm),'steps':steps}
        # Direct generic mcheckGX arithmetic, independent of the affine flow floor.
        mv=cn=cpa=0;slopes=[0]*Q;mass=[0]*Q
        for (i,j,a),(kind,m,p,r) in zip(TERMS,fs):
            z=LOOK[i,j];l=lo[z];u=max(l+1,hi[z]);base=sum(lo[i:j])
            l1,l2=f.weights(kind,m);const=1024-l1-l2;vp=f.PT.get(p,0);vr=f.PT.get(r,0)
            mv+=a*(const*f.lb(l,u)+l1*(vp&f.MASK32)+l2*(vr&f.MASK32))
            sp=(vp>>32)&f.MASK32;sr=(vr>>32)&f.MASK32;dp=vp>>64;dr=vr>>64
            cn+=a*(l1*max(2000000000-dp,0)*max(p-base,0)+l2*max(2000000000-dr,0)*max(r-base,0))
            cpa+=a*(l1*max(dp-2000000000,0)*max(p-base,0)+l2*max(dr-2000000000,0)*max(r-base,0))
            sl=a*(l1*sp+l2*sr);ma=a*(l1+l2)
            for z in range(i,j):slopes[z]+=sl;mass[z]+=ma
        pen=sum((u-l)*max(2000000000*ma+p-(1024000000000*b+sl+s),0)
            for u,l,ma,p,b,sl,s in zip(hi[:Q],lo[:Q],mass,pp,BS,slopes,ss))
        total=10240000000000*sum(b*l for b,l in zip(BS,lo[:Q]))+SC*mv+10*(cpa+cm)-10*(cn+cp+pen)
        rec['mcheck_numerator']=str(total);rec['mcheck_floor']=total/DEN
        rec['floor_numerator']=str(total);rec['floor']=total/DEN
    return rec

def cut(s,rec):
    lo,hi=s;g=np.array(rec['gaps']);best=None
    if 'relaxation_values' in rec:
        vals=kernel(np.array([sum(g[i:j]) for i,j,a in TERMS]))
        for t,(i,j,a) in enumerate(TERMS):
            z=LOOK[i,j]
            if hi[z]-lo[z]<2:continue
            # The frozen minorant library has no support beyond 16. Splitting
            # a cell wholly in that tail cannot improve its zero minorant.
            # Such a span must not dominate the adaptive error score forever.
            if lo[z]>=16*SC:continue
            error=max(0,vals[t]-rec['relaxation_values'][t])*a/D
            # Float is used only to choose the branch; every leaf remains exact.
            if best is None or error>best[0]:best=(error,z)
        if best is not None and best[0]>1e-10:
            z=best[1];l=lo[z];u=hi[z];i,j=ALL[z]
            if l<16*SC<u:return z,16*SC
            mid=round(sum(g[i:j])*SC)
            if not l+(u-l)//8<mid<u-(u-l)//8:mid=(l+u)//2
            return z,mid
        best=None
    for z,(i,j) in enumerate(ALL):
        if hi[z]-lo[z]<2:continue
        if lo[z]>=16*SC:continue
        # Prioritize the weighted kernel uncertainty at the LP minimizer.
        a=next((a for ii,jj,a in TERMS if ii==i and jj==j),0)
        width=(hi[z]-lo[z])/SC
        score=(a/D+.01)/(j-i)**.3*min(width,2.)
        if best is None or score>best[0]:best=(score,z)
    z=best[1];l=lo[z];u=hi[z]
    # Split broad intervals at half-integer kernel landmarks, retaining the
    # branch containing the LP optimizer first to expose hard basins quickly.
    mid=(l+u)//2
    landmarks=[int(x*SC/2) for x in range(2,67) if l+64<int(x*SC/2)<u-64]
    if landmarks:mid=min(landmarks,key=lambda x:abs(x-mid))
    return z,mid

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--max-nodes',type=int,default=1000)
    ap.add_argument('--output',default='prototype.json');ap.add_argument('--resume');ap.add_argument('--old-format',action='store_true');args=ap.parse_args()
    global OLD,LD,DEN,TARGET
    OLD=args.old_format
    if OLD:LD=1024*D;DEN=LD*WD;TARGET=433*(DEN//50000)
    start=time.time();r=root();todo=[(r,0,'r')];accepted=[];branches=[];checked=0;maxdepth=0
    if args.resume:
        old=json.loads(Path(args.resume).read_text());todo=[(x['state'],x['depth'],x['path']) for x in old['unresolved']]
        accepted=old['accepted'];branches=old['branches'];checked=old['checked']
    def save():
        out={'scope':'Exact arithmetic discovery only; each support relies on pinned PT/LB and coverage still needs Lean',
             'target':'433/50000','SC':SC,'denominator':str(DEN),'mixture_denominator':LD,'terms':TERMS,
             'format':'mcheckGX-1024' if OLD else 'arbitrary-lambda','pid':os.getpid(),
             'parameter_sha256':hashlib.sha256(PAR.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(f.SRC.read_bytes()).hexdigest(),
             'root':r,'checked':checked,'accepted_count':len(accepted),'unresolved_count':len(todo),'maxdepth':maxdepth,
             'elapsed_seconds':time.time()-start,'accepted':accepted,'branches':branches,
             'unresolved':[{'state':s,'depth':dep,'path':path} for s,dep,path in todo]}
        path=Path(__file__).with_name(args.output);temporary=path.with_suffix('.partial')
        temporary.write_text(json.dumps(out,separators=(',',':'))+'\n');temporary.replace(path)
        return out
    initial=checked
    while todo and checked-initial<args.max_nodes:
        s,depth,path=todo.pop();rec=certify(s,export=True);checked+=1;maxdepth=max(maxdepth,depth)
        if rec.get('empty') or int(rec.get('floor_numerator','-1'))>=TARGET:
            accepted.append({'path':path,'depth':depth,'result':rec})
        else:
            ax,q=cut(s,rec);left=split(s,ax,q,True);right=split(s,ax,q,False)
            branches.append({'path':path,'axis':ax,'cut':q})
            if right is not None:todo.append((right,depth+1,path+'1'))
            if left is not None:todo.append((left,depth+1,path+'0'))
        if checked%100==0:print(json.dumps({'checked':checked,'accepted':len(accepted),'pending':len(todo),
            'depth':maxdepth,'seconds':time.time()-start,'last_floor':rec.get('floor')}),flush=True)
        if checked%1000==0:save()
    out=save()
    print(json.dumps({k:v for k,v in out.items() if k not in ('accepted','branches','unresolved','root','terms')}),flush=True)
if __name__=='__main__':main()
