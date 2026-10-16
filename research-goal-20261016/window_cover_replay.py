"""Independent integer/geometry replay of a partial or complete new-window tree.

No LP solver output is trusted. Transcendental oracle enclosures are recomputed
with the recorded Fraction implementation, whose analytic connections remain
explicit proof obligations. This is numerical evidence, never Lean verification.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, sys, time

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
sys.path.insert(0,str(HERE))
import window_global_cover as w
g=w.g

def replay(data):
    global w,g
    if data['target']=='11/1250':
        import window_lower_global_cover as lower
        w=lower;g=w.g
    else:
        assert data['target']=='221/25000'
    for name,digest in data['input_sha256'].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,name
    branches={x['path']:x for x in data['branches']}
    leaves={x['path']:x for x in data['accepted']}
    front={x['path']:x for x in data['unresolved']}
    assert len(branches)==len(data['branches']) and len(leaves)==len(data['accepted']) and len(front)==len(data['unresolved'])
    assert not(set(branches)&set(leaves) or set(branches)&set(front) or set(leaves)&set(front))
    assert data['root']==[list(x) for x in w.root()]
    todo=[(w.root(),'r')];seen=set();counts={'value':0,'stationary':0,'reflection':0,'frontier':0,'implicit_empty':0}
    minimum=None
    while todo:
        state,path=todo.pop();seen.add(path);lo,hi=state
        if path in branches:
            b=branches[path];ax=b['axis'];q=b['cut'];assert lo[ax]<q<hi[ax]
            for suffix,upper in [('0',True),('1',False)]:
                child=g.split(state,ax,q,upper)
                if child is None:counts['implicit_empty']+=1
                else:todo.append((child,path+suffix))
            continue
        if path in front:
            assert front[path]['state']==[list(x) for x in state]
            counts['frontier']+=1;continue
        assert path in leaves,('uncovered',path)
        leaf=leaves[path];kind=leaf['kind'];counts[kind]+=1
        if kind=='reflection':assert hi[8]<lo[0];continue
        if kind=='stationary':
            # Recalculate signed partial bounds without trusting stored signs.
            rec=leaf['result']
            if isinstance(rec['direction'],list):
                import window_direction_probe as probe
                grid=ROOT/'research-goal-20261016/cover_newjet.json'
                digest=hashlib.sha256(grid.read_bytes()).hexdigest()
                assert digest==rec['derivative_grid_sha256']==data['derivative_grid_sha256']
                if not getattr(probe,'_replay_grid_installed',False):
                    assert probe.install_grid(grid)==digest
                    probe._replay_grid_installed=True
                d=rec['direction'];assert len(d)==9 and all(isinstance(v,int) for v in d)
                assert all(v>=0 or lo[i]>g.SEP for i,v in enumerate(d))
                if rec.get('kind')=='correlated_direction':
                    import cover_correlated_verify as independent
                    if not hasattr(independent,'_mixed_cover_table'):
                        independent._mixed_cover_table=independent.make_table(grid)
                    independent.verify(state,rec,w.P,independent._mixed_cover_table)
                    continue
                exact=probe.upper(d,probe.ranges(state))
                assert exact<0 and str(exact)==rec['upper_numerator']
                assert rec['denominator']==str(g.D*probe.w.DS)
                continue
            r=rec['coordinate'];dr=rec['direction']
            low=up=g.BS[r]*w.DS
            for i,j,a in g.TERMS:
                if i<=r<j:
                    z=g.LOOK[i,j];dl,du=w.derivative_range(lo[z],hi[z]);low+=a*dl;up+=a*du
            if dr==1:assert up<0 and str(up)==rec['gradient_upper']
            else:assert dr==-1 and lo[r]>g.SEP and low>0 and str(low)==rec['gradient_lower']
            continue
        assert kind=='value'
        rec=leaf['result'];cert=rec['certificate']
        assert cert['lower_bounds']==lo and cert['upper_bounds']==hi and cert['mixture_denominator']==g.LD
        mass=[0]*len(g.TERMS);intercept=0;coeff=[b*g.LD for b in g.BS]
        for t,p,weight0,const0,slope0 in cert['mixture']:
            weight,const,slope=map(int,[weight0,const0,slope0]);assert weight>0
            i,j,a=g.TERMS[t];z=g.LOOK[i,j];l,u=lo[z],hi[z]
            if p==-1:
                assert slope==0 and const==w.constant_lower(l,u)*g.SC
            else:
                assert p>=0
                pl,pu,v,sl,err=w.original_support(p)
                assert pl<=l and u<=pu
                assert const==g.SC*v-10*sl*p-10*err*max(p-l,0) and slope==10*sl
            mass[t]+=weight;intercept+=weight*const
            for r in range(i,j):coeff[r]+=weight*slope
        assert all(m<=a*(g.LD//g.D) for m,(_,_,a) in zip(mass,g.TERMS))
        assert str(intercept)==cert['intercept'] and list(map(str,coeff))==cert['gap_coefficients']
        cl=g.close(lo,hi);assert cl is not None and cl[:2]==(lo,hi)
        d=cl[2];flow=cert['flow'];div=[0]*10;cost=0
        for i,j,amount0,u in flow['nonzero_flow']:
            amount=int(amount0);assert amount>=0 and i!=j and u==d[i][j]
            div[i]+=amount;div[j]-=amount;cost+=amount*u
        expect=[-coeff[0]]+[coeff[r-1]-coeff[r] for r in range(1,9)]+[coeff[-1]]
        assert div==expect and list(map(str,div))==flow['divergence'] and str(cost)==flow['cost']
        exact=intercept-cost
        assert exact==int(rec['floor_numerator']) and exact>=g.TARGET
        minimum=exact if minimum is None else min(minimum,exact)
    assert seen==set(branches)|set(leaves)|set(front)
    assert data['checked']==len(branches)+len(leaves)
    return {'counts':counts,'nodes_replayed':len(seen),'checked_nodes':data['checked'],
            'exact_smallest_value_numerator':str(minimum),'denominator':str(g.DEN),
            'complete_numerical_cover':not front,'integer_flow_geometry_replay_passed':True,
            'analytic_supports_Lean_proven':False,'new_zero_proportion_proven':False}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('input',type=Path)
    ap.add_argument('--output',type=Path,default=HERE/'window-cover-replay.json');args=ap.parse_args()
    start=time.monotonic();raw=args.input.read_bytes();data=json.loads(raw);out=replay(data)
    out.update(scope=__doc__,input_sha256=hashlib.sha256(raw).hexdigest(),
        replay_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start)
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
