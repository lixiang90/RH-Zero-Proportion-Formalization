"""Ordered W10 global certificate search, preserving all frozen candidates.

Every node applies two exact Nat-cuB rounds. Existing unnormalised witnesses
are used only as hints and are checked again against the actual new cell.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, os, time
import compact_thin as thin
import tree_flow
g=thin.g;g.OLD=True;g.LD=1024*g.D;g.DEN=g.LD*g.WD;g.TARGET=433*(g.DEN//50000)
HERE=Path(__file__).parent;BB=1<<42;TB=2*BB
POINT={p:(pl,pu) for p,pl,pu,v,s,e in g.PT}

def rawsplit(s,ax,cut,upper):
    lo,hi=s;i,j=g.ALL[ax];a,b,w=(i,j,cut) if upper else (j,i,-cut)
    def leg(x,y):return 0 if x==y else hi[g.LOOK[x,y]] if x<y else -lo[g.LOOK[y,x]]
    col=[max(0,BB+leg(x,a)) for x in range(10)]
    row=[max(0,BB+w+leg(b,x)) for x in range(10)]
    return ([max(v,max(0,TB-col[j]-row[i])) for v,(i,j) in zip(lo,g.ALL)],
            [min(v,max(0,col[i]+row[j]-TB)) for v,(i,j) in zip(hi,g.ALL)])

def normalize(s):
    cuts=[]
    for _ in range(2):
        q=s[1][8];s=rawsplit(s,0,q,True);cuts.append(q)
        q=s[0][0];s=rawsplit(s,8,q,False);cuts.append(q)
    if all(l<=u for l,u in zip(*s)):
        cl=g.close(*s);assert cl is not None and cl[:2]==s
    return s,cuts

def hint_check(s,h):
    fs=h['FS'];steps=h['steps'];lo,hi=s
    for (i,j,a),(k,m,p,r) in zip(g.TERMS,fs):
        z=g.LOOK[i,j];l=lo[z];u=hi[z];w1,w2=g.f.weights(k,m)
        for w,p in [(w1,p),(w2,r)]:
            if w:
                pl,pu=POINT.get(p,(0,0))
                if not pl<=l<=p<=u<=pu:return None
    total=tree_flow.value(fs,lo,hi,steps)
    if total<g.TARGET:return None
    pp,ss,cp,cm=thin.dual_state(lo,hi,steps)
    return {'floor_numerator':str(total),'floor':total/g.DEN,'mcheck_numerator':str(total),
        'mcheck_floor':total/g.DEN,'FS':fs,'reused_hint':True,
        'multiplier':{'P':list(map(str,pp)),'S':list(map(str,ss)),'Cp':str(cp),'Cm':str(cm),'steps':steps},
        'certificate':{'lower_bounds':lo,'upper_bounds':hi}}

def make_seeds():
    sources=['parallel-master.json','parallel-0.json','parallel-1-master.json','parallel-2.json']+[f'parallel-1-{i}.json' for i in range(3)]
    nodes={};leaves={};hashes={}
    for name in sources:
        raw=(HERE/name).read_bytes();x=json.loads(raw);hashes[name]=hashlib.sha256(raw).hexdigest()
        for z in x['branches']:
            assert z['path'] not in nodes;nodes[z['path']]=z
        for z in x['accepted']:
            assert z['path'] not in leaves
            r=z['result']
            if 'FS' in r:leaves[z['path']]={'FS':r['FS'],'steps':r['multiplier']['steps']}
    root=g.root();rnorm,rcuts=normalize(root)
    # Fixed total-span partition: <=14, 14..20, >=20.
    left=rawsplit(rnorm,16,14*g.SC,True);right=rawsplit(rnorm,16,14*g.SC,False)
    rightnorm,_=normalize(right)
    mid=rawsplit(rightnorm,16,20*g.SC,True);high=rawsplit(rightnorm,16,20*g.SC,False)
    master={'scope':'Ordered W10 partition scaffold, all nodes normalize twice','root':root,
        'normalize_rounds':2,'format':'ordered-mcheckGX-1024','checked':2,'accepted':[],
        'branches':[{'path':'r','axis':16,'cut':14*g.SC},{'path':'r1','axis':16,'cut':20*g.SC}],
        'source_checkpoints_sha256':hashes,
        'unresolved':[{'path':'r0','state':left,'depth':1,'old_path':'r00'},
            {'path':'r10','state':mid,'depth':2,'old_path':'r01'},
            {'path':'r11','state':high,'depth':2,'old_path':'r1'}]}
    (HERE/'ordered-master.json').write_text(json.dumps(master,separators=(',',':'))+'\n')
    for i,(oldprefix,seed) in enumerate(zip(['r00','r01','r1'],master['unresolved'])):
        (HERE/f'ordered-hints-{i}.json').write_text(json.dumps({'branches':{p:z for p,z in nodes.items() if p.startswith(oldprefix)},
            'leaves':{p:z for p,z in leaves.items() if p.startswith(oldprefix)}},separators=(',',':'))+'\n')
        (HERE/f'ordered-seed-{i}.json').write_text(json.dumps({**master,'checked':0,'branches':[],'unresolved':[seed]},separators=(',',':'))+'\n')
    print(json.dumps({'scaffold_created':True,'old_branch_hints':len(nodes),'old_leaf_hints':len(leaves)}),flush=True)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--make-seeds',action='store_true');ap.add_argument('--resume',type=Path)
    ap.add_argument('--hints',type=Path);ap.add_argument('--output',type=Path);ap.add_argument('--max-nodes',type=int,default=1000000)
    ap.add_argument('--adaptive',action='store_true');args=ap.parse_args()
    if args.make_seeds:make_seeds();return
    doc=json.loads(args.resume.read_text());hints=json.loads(args.hints.read_text());oldnodes=hints['branches'];oldleaves=hints['leaves'];near={}
    def nearby(p):
        if p is None:return []
        if p in near:return near[p]
        if p in oldleaves:out=[p]
        elif p in oldnodes:out=(nearby(p+'0')[:1]+nearby(p+'1')[:1])[:2]
        else:out=[]
        near[p]=out;return out
    todo=doc['unresolved'];accepted=doc['accepted'];branches=doc['branches'];checked=doc['checked'];initial=checked
    start=time.monotonic();reused=0;maxdepth=0
    def save():
        out={'scope':'Exact arithmetic ordered search; full Lean coverage still requires replay',
            'format':'ordered-mcheckGX-1024','normalize_rounds':2,'root':g.root(),'target':'433/50000',
            'parameter_sha256':hashlib.sha256(g.PAR.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(g.f.SRC.read_bytes()).hexdigest(),
            'pid':os.getpid(),'checked':checked,'accepted_count':len(accepted),'unresolved_count':len(todo),
            'adaptive_new_branches':args.adaptive,
            'elapsed_seconds':time.monotonic()-start,'maxdepth':maxdepth,'reused_hints':reused,
            'terms':g.TERMS,'denominator':str(g.DEN),'SC':g.SC,'mixture_denominator':g.LD,
            'accepted':accepted,'branches':branches,'unresolved':todo}
        tmp=args.output.with_suffix('.partial');tmp.write_text(json.dumps(out,separators=(',',':'))+'\n');tmp.replace(args.output)
        return out
    while todo and checked-initial<args.max_nodes:
        row=todo.pop();path=row['path'];depth=row['depth'];oldpath=row.get('old_path');s,cuts=normalize(row['state'])
        checked+=1;maxdepth=max(depth,maxdepth)
        invalid=next((i for i,(l,u) in enumerate(zip(*s)) if u<l),None)
        if invalid is not None:
            accepted.append({'path':path,'depth':depth,'normalize_rounds':2,'normalize_cuts':cuts,
                'result':{'empty':True,'violation_axis':invalid,'certificate':{'lower_bounds':s[0],'upper_bounds':s[1]}}});continue
        while oldpath in oldnodes:
            z=oldnodes[oldpath];l=s[0][z['axis']];u=s[1][z['axis']]
            if z['cut']<=l:oldpath+='1'
            elif u<=z['cut']:oldpath+='0'
            else:break
        rec=None
        for hp in nearby(oldpath):
            rec=hint_check(s,oldleaves[hp])
            if rec is not None:reused+=1;break
        if rec is None:rec=g.certify(s,True)
        if rec.get('empty') or int(rec.get('floor_numerator','-1'))>=g.TARGET:
            accepted.append({'path':path,'depth':depth,'normalize_rounds':2,'normalize_cuts':cuts,'result':rec})
        else:
            if oldpath in oldnodes and not args.adaptive:
                z=oldnodes[oldpath];ax=z['axis'];cut=z['cut'];op0=oldpath+'0';op1=oldpath+'1'
            else:ax,cut=g.cut(s,rec);op0=op1=oldpath if args.adaptive else None
            branches.append({'path':path,'axis':ax,'cut':cut,'normalize_rounds':2,'normalize_cuts':cuts})
            todo.append({'path':path+'1','depth':depth+1,'state':rawsplit(s,ax,cut,False),'old_path':op1})
            todo.append({'path':path+'0','depth':depth+1,'state':rawsplit(s,ax,cut,True),'old_path':op0})
        if checked%100==0:print(json.dumps({'checked':checked,'accepted':len(accepted),'pending':len(todo),
            'maxdepth':maxdepth,'hint_closed':reused,'seconds':time.monotonic()-start}),flush=True)
        if checked%1000==0:save()
    out=save();print(json.dumps({k:out[k] for k in ['checked','accepted_count','unresolved_count','maxdepth','reused_hints','elapsed_seconds']}),flush=True)
if __name__=='__main__':main()
