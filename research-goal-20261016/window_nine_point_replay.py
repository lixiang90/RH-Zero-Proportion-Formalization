"""Exact replay of the nine-point pilot; no LP or flow optimizer is called.

Geometry is rebuilt by full difference-constraint closure independently of
the producer's single-edge update. Scalar rational intervals are recomputed;
their actual-function Lean bridge is still an explicit remaining obligation.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,time
import window_nine_point_cover as case
w=case.w;g=case.g;HERE=Path(__file__).parent;ROOT=HERE.parent

def close(state):
    d=[[0 if i==j else 10**18 for j in range(g.N)] for i in range(g.N)]
    for (i,j),lo,hi in zip(g.ALL,*state):d[i][j]=hi;d[j][i]=-lo
    for k in range(g.N):
        for i in range(g.N):
            for j in range(g.N):d[i][j]=min(d[i][j],d[i][k]+d[k][j])
    if any(d[i][i]<0 for i in range(g.N)):return None
    return [[-d[j][i] for i,j in g.ALL],[d[i][j] for i,j in g.ALL]],d

def replay(doc):
    assert doc['format']=='nine-point-rational-value-KKT-pilot-v1' and doc['target']=='433/50000'
    for name,sha in doc['input_sha256'].items():assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==sha,name
    root=[list(x) for x in case.root()];assert doc['root']==root
    branches={r['path']:r for r in doc['branches']};leaves={r['path']:r for r in doc['accepted']};front={r['path']:r for r in doc['unresolved']}
    assert len(branches)==len(doc['branches']) and len(leaves)==len(doc['accepted']) and len(front)==len(doc['unresolved'])
    assert not(set(branches)&set(leaves) or set(branches)&set(front) or set(leaves)&set(front))
    todo=[(root,'r')];seen=set();counts={'value':0,'reflection':0,'stationary':0,'frontier':0,'implicit_empty':0}
    while todo:
        state,path=todo.pop();seen.add(path);cl=close(state);assert cl is not None and cl[0]==state
        lo,hi=state
        if path in branches:
            b=branches[path];z=b['axis'];q=b['cut'];assert lo[z]<q<hi[z]
            for bit in ['0','1']:
                # bit 0 means upper <= cut; bit 1 means lower >= cut.
                child=[lo.copy(),hi.copy()]
                child[1 if bit=='0' else 0][z]=q
                out=close(child)
                if out is None:counts['implicit_empty']+=1
                else:todo.append((out[0],path+bit))
            continue
        if path in front:assert front[path]['state']==state;counts['frontier']+=1;continue
        assert path in leaves,('uncovered path',path)
        row=leaves[path];kind=row['kind'];counts[kind]+=1
        if kind=='reflection':assert hi[g.Q-1]<lo[0];continue
        rec=row['result']
        if kind=='stationary':
            r=rec['coordinate'];dr=rec['direction'];lower=upper=g.BS[r]*w.DS
            for i,j,a in g.TERMS:
                if i<=r<j:
                    z=g.LOOK[i,j];dl,du=w.derivative_range(lo[z],hi[z]);lower+=a*dl;upper+=a*du
            assert rec['gradient_denominator']==str(g.D*w.DS)
            if dr==1:assert upper<0 and rec['gradient_upper']==str(upper)
            else:assert dr==-1 and lo[r]>g.SEP and lower>0 and rec['gradient_lower']==str(lower)
            continue
        assert kind=='value';cert=rec['certificate'];assert cert['lower_bounds']==lo and cert['upper_bounds']==hi and cert['mixture_denominator']==g.LD
        mass=[0]*len(g.TERMS);C=0;coeff=[b*g.LD for b in g.BS]
        for t,p,weight0,const0,slope0 in cert['mixture']:
            weight,const,slope=map(int,[weight0,const0,slope0]);assert weight>0
            i,j,a=g.TERMS[t];z=g.LOOK[i,j];l,u=lo[z],hi[z]
            if p==-1:assert slope==0 and const==w.constant_lower(l,u)*g.SC
            else:
                assert p>=0;pl,pu,v,sl,err=w.original_support(p);assert pl<=l and u<=pu
                assert const==g.SC*v-10*sl*p-10*err*max(p-l,0) and slope==10*sl
            mass[t]+=weight;C+=weight*const
            for r in range(i,j):coeff[r]+=weight*slope
        assert all(m<=a*(g.LD//g.D) for m,(_,_,a) in zip(mass,g.TERMS))
        assert str(C)==cert['intercept'] and list(map(str,coeff))==cert['gap_coefficients']
        flow=cert['flow'];balance=[0]*g.N;cost=0
        for i,j,y0,u in flow['nonzero_flow']:
            y=int(y0);assert y>=0 and i!=j and u==cl[1][i][j]
            balance[i]+=y;balance[j]-=y;cost+=y*u
        expected=[-coeff[0]]+[coeff[r-1]-coeff[r] for r in range(1,g.Q)]+[coeff[-1]]
        assert balance==expected==list(map(int,flow['divergence'])) and cost==int(flow['cost'])
        assert C-cost==int(rec['floor_numerator']) and C-cost>=g.TARGET
    assert seen==set(branches)|set(leaves)|set(front) and doc['checked']==len(branches)+len(leaves)
    return {'counts':counts,'nodes_replayed':len(seen),'all_passed':True,
      'complete_numerical_cover':not front,'actual_scalar_Lean_proven':False,'new_zero_proportion_proven':False}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'window-nine-point-cover.json')
    ap.add_argument('--output',type=Path,default=HERE/'window-nine-point-cover-replay.json');args=ap.parse_args();start=time.monotonic()
    stored=args.input.read_bytes();raw=gzip.decompress(stored) if args.input.suffix=='.gz' else stored
    out=replay(json.loads(raw));out.update(scope=__doc__,input_sha256=hashlib.sha256(raw).hexdigest(),
      archive_sha256=hashlib.sha256(stored).hexdigest() if args.input.suffix=='.gz' else None,
      replay_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start)
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
