"""Encode the exact affine dual by a 27-bit ten-vertex tree.

The support coefficients determine its signed edge flow. No optimizer output
is trusted: decoded flows are replayed through the same integer inequality.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, time
import networkx as nx
import compact_thin as thin
g=thin.g;Q=9;N=10

def slope(fs):
    coeff=[1024000000000*b for b in g.BS]
    for (i,j,a),(k,m,p,r) in zip(g.TERMS,fs):
        l1,l2=g.f.weights(k,m)
        sp=((g.f.PT.get(p,0)>>32)&g.f.MASK32)-2000000000
        sr=((g.f.PT.get(r,0)>>32)&g.f.MASK32)-2000000000
        sl=a*(l1*sp+l2*sr)
        for z in range(i,j):coeff[z]+=sl
    return coeff

def divergence(fs):
    c=slope(fs)
    return [-c[0]]+[c[i-1]-c[i] for i in range(1,Q)]+[c[-1]]

def encode(edges):
    adj=[set() for i in range(N)]
    for i,j in edges:adj[i].add(j);adj[j].add(i)
    seq=[]
    for k in range(N-2):
        i=min(i for i in range(N) if len(adj[i])==1)
        j=next(iter(adj[i]));seq.append(j);adj[i].remove(j);adj[j].remove(i)
    assert len(seq)==8
    code=sum(x*10**k for k,x in enumerate(seq))
    return code

def decode(code):
    seq=[(code//10**k)%10 for k in range(8)]
    deg=[1+seq.count(i) for i in range(N)];edges=[]
    for j in seq:
        i=min(i for i in range(N) if deg[i]==1)
        edges.append((min(i,j),max(i,j)));deg[i]-=1;deg[j]-=1
    i,j=[i for i in range(N) if deg[i]==1]
    edges.append((min(i,j),max(i,j)))
    return edges

def moves(fs,code):
    div=divergence(fs);edges=decode(code);out=[];signed=[]
    for a,b in edges:
        seen={a}
        for _ in range(9):
            for i,j in edges:
                if (i,j)==(a,b):continue
                if i in seen or j in seen:seen.update((i,j))
        assert b not in seen
        y=sum(div[i] for i in seen)
        signed.append((a,b,y))
        if b>a+1 and y:out.append([a,b,y>0,str(abs(y))])
    assert sum(div)==0
    rebuilt=[0]*10
    for i,j,y in signed:rebuilt[i]+=y;rebuilt[j]-=y
    assert rebuilt==div
    return out

def value(fs,lo,hi,steps):
    pp,ss,cp,cm=thin.dual_state(lo,hi,steps)
    cs=[thin.term_contribution(t,x,lo,hi) for t,x in enumerate(fs)]
    v=[sum(c[z] for c in cs) for z in range(19)]
    pen=sum((u-l)*max(2000000000*v[10+r]+pp[r]-(1024000000000*b+v[1+r]+ss[r]),0)
        for r,(u,l,b) in enumerate(zip(hi[:Q],lo[:Q],g.BS)))
    return 10240000000000*sum(b*l for b,l in zip(g.BS,lo[:Q]))+10*(cm-cp)+v[0]-10*pen

def recompute(fs,lo,hi):
    cl=g.close(lo,hi);assert cl is not None and cl[:2]==(lo,hi)
    div=divergence(fs);graph=nx.DiGraph()
    for i in range(N):graph.add_node(i,demand=-div[i])
    for i in range(N):
        for j in range(N):
            if i!=j:graph.add_edge(i,j,weight=cl[2][i][j])
    cost,flow=nx.network_simplex(graph)
    edges=[];uf=list(range(N))
    def find(i):
        while uf[i]!=i:i=uf[i]
        return i
    for i,row in flow.items():
        for j,y in row.items():
            if not y:continue
            ii,jj=find(i),find(j)
            assert ii!=jj,('Non-forest simplex output',i,j,y)
            uf[ii]=jj;edges.append((min(i,j),max(i,j)))
    # Complete every forest with zero-flow adjacent edges. Adding such an edge
    # connects components whose total divergence is zero.
    for i in range(N-1):
        ii,jj=find(i),find(i+1)
        if ii!=jj:uf[ii]=jj;edges.append((i,i+1))
    assert len(edges)==9
    code=encode(edges);assert set(decode(code))==set(edges)
    steps=moves(fs,code)
    total=value(fs,lo,hi,steps)
    assert total>=thin.THRESH,('Encoded dual failed',code,total)
    return {'tree_code':code,'dual_bits':27,'after_numerator':str(total),'steps':steps}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=Path(__file__).with_name('parallel-master.json'))
    ap.add_argument('--output',type=Path,default=Path(__file__).with_name('tree-flow-100.json'));ap.add_argument('--limit',type=int,default=100)
    args=ap.parse_args();raw=args.input.read_bytes();doc=json.loads(raw);started=time.monotonic();out=[]
    leaves=[x for x in doc['accepted'] if 'FS' in x['result']]
    for x in leaves[:args.limit or None]:
        r=x['result'];tr=thin.leaf_thin(r);fs=tr['FS'];lo=r['certificate']['lower_bounds'];hi=r['certificate']['upper_bounds']
        d=recompute(fs,lo,hi);assert int(d['after_numerator'])>=int(tr['after_numerator'])
        out.append({'path':x['path'],'FS':fs,'fs_word_hex':tr['fs_word_hex'],'fs_bits':tr['fs_bits'],
            'before_fs_bits':tr['before_bits'],'thin_numerator':tr['after_numerator'],**d})
    report={'scope':'Exact tree-dual compression only; not a full coverage proof',
        'source_sha256':hashlib.sha256(raw).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'input':str(args.input),'processed':len(out),'all_passed_exact_checker':True,
        'fs_bits_before':sum(x['before_fs_bits'] for x in out),'fs_bits_after':sum(x['fs_bits'] for x in out),
        'dual_bits_after':27*len(out),'seconds':time.monotonic()-started}
    args.output.write_text(json.dumps({'stats':report,'leaves':out},separators=(',',':'))+'\n')
    print(json.dumps(report),flush=True)
if __name__=='__main__':main()
