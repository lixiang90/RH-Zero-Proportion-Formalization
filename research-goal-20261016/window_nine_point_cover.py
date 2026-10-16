"""Eight-dimensional cover discovery for the rational nine-point alternative.

Every exported value bound uses capacity-valid integer mixtures and exact
flow. Local convexity evidence is regenerated for this window. This pilot
does not reuse ten-point scalar bounds or claim a Lean/global theorem.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,json,os,time
import numpy as np
import window_global_cover as w
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
PARAM=HERE/'window-nine-point-rational.json';CONVEX=HERE/'window-nine-point-convex.json'
P=json.loads(PARAM.read_bytes());g=w.g;ik=w.ik
g.N=9;g.Q=8;g.P=P;g.PAR=PARAM;g.BS=P['b_numerators']
g.ALL=[(i,i+1) for i in range(g.Q)]+[(i,j) for i in range(g.Q) for j in range(i+2,g.N)]
g.LOOK={p:i for i,p in enumerate(g.ALL)};g.TERMS=[tuple(t) for t in P['a_upper'] if t[2]]
g.TARGET=433*(g.DEN//50000)
ik.PARAM=PARAM;ik.DATA=P;ik.COEFF=[F(1)]+[F(v,10**9) for v in P['window_coefficient_numerators_1e9']]
ik.kernel_jet.cache_clear();w.COEFF=np.array(list(map(float,ik.COEFF)))

def root():
    extra=86600000*w.SC-sum(g.BS)*g.SEP
    assert extra>0 and all(b>0 for b in g.BS)
    up=[g.SEP+w.ceil(F(extra,b)) for b in g.BS]
    lo=[(j-i)*g.SEP for i,j in g.ALL];hi=[sum(up[i:j]) for i,j in g.ALL]
    for z,(i,j) in enumerate(g.ALL):
        hi[z]=min(hi[z],(j-i)*g.SEP+w.ceil(F(extra,min(g.BS[i:j]))))
    cl=g.close(lo,hi);assert cl is not None and cl[:2]==(lo,hi)
    return lo,hi
g.root=root

def directional(state):
    low=[b*w.DS for b in g.BS];up=low.copy()
    for i,j,a in g.TERMS:
        z=g.LOOK[i,j];dl,du=w.derivative_range(state[0][z],state[1][z])
        for r in range(i,j):low[r]+=a*dl;up[r]+=a*du
    for r in range(g.Q):
        if up[r]<0:return {'coordinate':r,'direction':1,'gradient_upper':str(up[r]),'gradient_denominator':str(g.D*w.DS)}
        if low[r]>0 and state[0][r]>g.SEP:
            return {'coordinate':r,'direction':-1,'gradient_lower':str(low[r]),'gradient_denominator':str(g.D*w.DS)}
    return None

def prepare():
    start=time.monotonic();rows=[]
    for n in range(1,17):
        row=ik.convex_certificate(n,F(n)-F(21,100),F(n)+F(21,100));assert row['positive']
        rows.append(row)
    CONVEX.write_text(json.dumps({'scope':__doc__,'parameter_sha256':hashlib.sha256(PARAM.read_bytes()).hexdigest(),
      'regions':rows,'all_positive':True,'actual_kernel_Lean_proven':False,'seconds':time.monotonic()-start},separators=(',',':'))+'\n',encoding='utf8')
    print(json.dumps({'convex_regions':16,'seconds':time.monotonic()-start}),flush=True)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--prepare',action='store_true');ap.add_argument('--max-nodes',type=int,default=2500)
    ap.add_argument('--resume',type=Path);ap.add_argument('--output',type=Path,default=HERE/'window-nine-point-cover.json');args=ap.parse_args()
    if args.prepare:prepare()
    cv=json.loads(CONVEX.read_bytes());assert cv['all_positive'] and cv['parameter_sha256']==hashlib.sha256(PARAM.read_bytes()).hexdigest()
    files=[Path(__file__),Path(w.__file__),Path(ik.__file__),Path(g.__file__),PARAM,CONVEX]
    hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    todo=[(root(),0,'r')];accepted=[];branches=[];checked=0;depthmax=0;start=time.monotonic()
    if args.resume:
        old=json.loads(args.resume.read_bytes());assert old['input_sha256']==hashes
        todo=[(r['state'],r['depth'],r['path']) for r in old['unresolved']]
        accepted=old['accepted'];branches=old['branches'];checked=old['checked'];depthmax=old['maxdepth']
    def save():
        assert hashes=={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
        out={'scope':__doc__,'format':'nine-point-rational-value-KKT-pilot-v1','input_sha256':hashes,
          'target':'433/50000','SC':w.SC,'denominator':str(g.DEN),'separation':'123/128','pid':os.getpid(),
          'root':root(),'checked':checked,'maxdepth':depthmax,'accepted_count':len(accepted),
          'stationary_count':sum(r['kind']=='stationary' for r in accepted),'unresolved_count':len(todo),
          'accepted':accepted,'branches':branches,'unresolved':[{'state':s,'depth':d,'path':p} for s,d,p in todo],
          'tangent_data':[[p,*w.original_support(p)] for p in sorted(w.USED_SUPPORTS)],
          'global_floor_Lean_proven':False,'new_zero_proportion_proven':False,'submission_ready':False,
          'seconds':time.monotonic()-start}
        temp=args.output.with_suffix('.partial');temp.write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8');temp.replace(args.output)
    initial=checked
    while todo and checked-initial<args.max_nodes:
        s,depth,path=todo.pop();checked+=1;depthmax=max(depthmax,depth)
        if s[1][g.Q-1]<s[0][0]:accepted.append({'path':path,'depth':depth,'kind':'reflection'});continue
        rec=w.certify(s)
        if int(rec.get('floor_numerator','-1'))>=g.TARGET:accepted.append({'path':path,'depth':depth,'kind':'value','result':rec})
        else:
            excl=directional(s)
            if excl:accepted.append({'path':path,'depth':depth,'kind':'stationary','result':excl})
            else:
                ax,q=g.cut(s,rec);assert s[0][ax]<q<s[1][ax]
                branches.append({'path':path,'axis':ax,'cut':q})
                for bit,upper in [('1',False),('0',True)]:
                    child=g.split(s,ax,q,upper)
                    if child is not None:todo.append((child,depth+1,path+bit))
        if checked%250==0:print(json.dumps({'checked':checked,'accepted':len(accepted),'frontier':len(todo),'seconds':time.monotonic()-start}),flush=True)
        if checked%1000==0:save()
    save()
if __name__=='__main__':main()
