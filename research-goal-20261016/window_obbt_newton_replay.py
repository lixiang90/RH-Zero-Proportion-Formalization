"""Replay a full/partial KKT-minimizer tree with explicit contraction maps.

Contraction chains are checked by the independent stdlib verifier BEFORE
processing the refined node. No contraction is mistaken for a pointwise
cover. Value mixtures/flows, directional exclusions, Gram membership and all
tree/frontier edges are replayed. The separate 69-Gram arithmetic receipt
must also be checked; all actual-kernel and global-minimum Lean bridges
remain explicit obligations.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,time
import window_global_cover as high
import window_lower_global_cover as low
import window_direction_probe as direction
import cover_correlated_verify as correlated
import cover_contractor_verify as newton
import cover_gram_basin_api as gram
import cover_sublevel_obbt_verify_api as obbt
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent

def replay(data):
    w=low if data['target']=='11/1250' else high;g=w.g
    assert data['target'] in ['11/1250','221/25000'] and data['format']=='RelevantBelow-KKT-OBBT-v1'
    for name,digest in data['input_sha256'].items():assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,name
    assert data['root']==[list(x) for x in w.root()]
    grid=HERE/'cover_newjet.json';grid_sha=hashlib.sha256(grid.read_bytes()).hexdigest()
    assert grid_sha==data['derivative_grid_sha256'];direction.install_grid(grid)
    table=correlated.make_table(grid);registry=gram.make_gram_registry();assert registry['sha256']==data['Gram_certificate_sha256']
    original=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    assert original['a_upper']==w.P['a_upper'] and original['b_numerators']==w.P['b_numerators']
    branches={r['path']:r for r in data['branches']};leaves={r['path']:r for r in data['accepted']};frontier={r['path']:r for r in data['unresolved']};contractions=data['contractions'];sublevel=data['sublevel_contractions']
    assert len(branches)==len(data['branches']) and len(leaves)==len(data['accepted']) and len(frontier)==len(data['unresolved'])
    assert not(set(branches)&set(leaves) or set(branches)&set(frontier) or set(leaves)&set(frontier))
    counts={'value':0,'stationary':0,'Gram':0,'reflection':0,'stationary_empty':0,'frontier':0,'implicit_empty':0,'contraction_paths':0,'contraction_steps':0,'sublevel_paths':0,'sublevel_bounds':0,'sublevel_empty':0}
    todo=[(w.root(),'r')];seen=set();usedcontractions=set();usedsublevel=set();minimum=None
    while todo:
        state,path=todo.pop();state=[list(state[0]),list(state[1])];seen.add(path)
        if path in sublevel:
            usedsublevel.add(path);counts['sublevel_paths']+=1;counts['sublevel_bounds']+=len(sublevel[path]['certificates'])
            state=obbt.verify_step(state,sublevel[path],g.TARGET)
            if state is None:
                assert path not in contractions and path in leaves and leaves[path]['kind']=='sublevel_empty'
                counts['sublevel_empty']+=1
                continue
        if path in contractions:
            usedcontractions.add(path);counts['contraction_paths']+=1
            for step in contractions[path]:
                assert state is not None
                state=newton.verify_step(state,step,w.P,table);counts['contraction_steps']+=1
        if state is None:
            assert path in leaves and leaves[path]['kind']=='stationary_empty';counts['stationary_empty']+=1
            continue
        lo,hi=state
        if path in branches:
            b=branches[path];ax=b['axis'];cut=b['cut'];assert lo[ax]<cut<hi[ax]
            for bit,upper in [('1',False),('0',True)]:
                child=newton.a.child(state,ax,cut,upper)
                if child is None:counts['implicit_empty']+=1
                else:todo.append((child,path+bit))
            continue
        if path in frontier:
            assert frontier[path]['state']==state;counts['frontier']+=1;continue
        assert path in leaves,('missing minimizer leaf',path);row=leaves[path];kind=row['kind'];counts[kind]+=1
        if kind=='reflection':assert hi[8]<lo[0];continue
        rec=row['result']
        if kind=='Gram':gram.verify(state,rec,data['target'],registry);continue
        if kind=='stationary':
            if isinstance(rec['direction'],list):
                assert rec['derivative_grid_sha256']==grid_sha
                if rec.get('kind')=='correlated_direction':correlated.verify(state,rec,w.P,table);continue
                d=rec['direction'];assert len(d)==9 and all(isinstance(v,int) for v in d) and all(v>=0 or lo[i]>g.SEP for i,v in enumerate(d))
                value=direction.upper(d,direction.ranges(state))
                assert value<0 and str(value)==rec['upper_numerator'] and rec['denominator']==str(g.D*direction.w.DS)
            else:
                r=rec['coordinate'];dr=rec['direction'];lower=upper=g.BS[r]*w.DS
                for i,j,a in g.TERMS:
                    if i<=r<j:
                        z=g.LOOK[i,j];dl,du=w.derivative_range(lo[z],hi[z]);lower+=a*dl;upper+=a*du
                if dr==1:assert upper<0 and str(upper)==rec['gradient_upper']
                else:assert dr==-1 and lo[r]>g.SEP and lower>0 and str(lower)==rec['gradient_lower']
            continue
        assert kind=='value'
        cert=rec['certificate'];assert cert['lower_bounds']==lo and cert['upper_bounds']==hi and cert['mixture_denominator']==g.LD
        mass=[0]*len(g.TERMS);intercept=0;coeff=[b*g.LD for b in g.BS]
        for t,p,weight0,const0,slope0 in cert['mixture']:
            weight,const,slope=map(int,[weight0,const0,slope0]);assert weight>0
            i,j,a=g.TERMS[t];z=g.LOOK[i,j];l,u=lo[z],hi[z]
            if p==-1:assert slope==0 and const==w.constant_lower(l,u)*g.SC
            else:
                assert p>=0;pl,pu,v,sl,err=w.original_support(p)
                assert pl<=l and u<=pu and const==g.SC*v-10*sl*p-10*err*max(p-l,0) and slope==10*sl
            mass[t]+=weight;intercept+=weight*const
            for r in range(i,j):coeff[r]+=weight*slope
        assert all(m<=a*(g.LD//g.D) for m,(_,_,a) in zip(mass,g.TERMS))
        assert str(intercept)==cert['intercept'] and list(map(str,coeff))==cert['gap_coefficients']
        flow=cert['flow'];balance=[0]*10;cost=0
        for i,j,y0,u in flow['nonzero_flow']:
            y=int(y0);assert y>=0 and i!=j and u==newton.a.edge_value(state,i,j)
            balance[i]+=y;balance[j]-=y;cost+=y*u
        desired=[-coeff[0]]+[coeff[i-1]-coeff[i] for i in range(1,9)]+[coeff[-1]]
        assert balance==desired==list(map(int,flow['divergence'])) and cost==int(flow['cost'])
        value=intercept-cost;assert value==int(rec['floor_numerator']) and value>=g.TARGET
        minimum=value if minimum is None else min(minimum,value)
    assert seen==set(branches)|set(leaves)|set(frontier) and usedcontractions==set(contractions) and usedsublevel==set(sublevel)
    assert counts['sublevel_paths']==data['sublevel_contraction_paths'] and counts['sublevel_bounds']==data['sublevel_bounds']
    assert data['checked']==len(branches)+len(leaves) and counts['contraction_steps']==data['contraction_steps'] and counts['contraction_paths']==data['contraction_paths']
    return {'counts':counts,'nodes_replayed':len(seen),'checked_nodes':data['checked'],'exact_minimum_value_numerator':str(minimum),
      'sublevel_only_OBBT_replayed':True,'KKT_only_contractions_replayed':True,'pointwise_cover_asserted':False,'complete_finite_minimizer_partition':not frontier,
      'separate_Gram_certificate_replay_required':True,'actual_analytic_Lean_bridges_complete':False,'new_zero_proportion_proven':False}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('input',type=Path);ap.add_argument('--output',type=Path,default=HERE/'window-obbt-newton-replay.json')
    args=ap.parse_args();start=time.monotonic();raw=args.input.read_bytes()
    if args.input.suffix=='.gz':raw=gzip.decompress(raw)
    result=replay(json.loads(raw));result.update(scope=__doc__,input_sha256=hashlib.sha256(raw).hexdigest(),
      script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),independent_verifier_sources={**newton.source_hashes(),**obbt.source_hashes()},seconds=time.monotonic()-start)
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf8');print(json.dumps(result),flush=True)
if __name__=='__main__':main()
