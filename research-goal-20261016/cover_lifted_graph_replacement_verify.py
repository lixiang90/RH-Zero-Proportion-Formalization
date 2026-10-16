"""Verify complete old local subtrees and their replacement by thirteen graph leaves.

Run with python -S: only the standard library and rational scalar routines
are available.  Both old and new local trees are checked; omitted ancestor
siblings remain open external obligations, never claimed as a global cover.
"""
from pathlib import Path
from fractions import Fraction as F
import gzip,hashlib,json,sys,time
import cover_exact_scalar_replay as scalar_adapter
scalar_adapter.install()
import cover_lifted_graph_verify as graph
import cover_compact_codec as codec
import cover_sublevel_obbt_verify as obbt
import cover_sublevel_verify as energy
import cover_contractor_verify as newton
import cover_correlated_verify as correlated
HERE=Path(__file__).parent;ROOT=HERE.parent;SC=graph.SC;DS=graph.DS;a=graph.a
sha=lambda b:hashlib.sha256(b).hexdigest()


def stationary(state,result,params,checker):
    if result.get('kind')=='correlated_direction':correlated.verify(state,result,params,checker.scalar);return
    d=result['direction'];assert isinstance(d,list) and len(d)==9 and all(isinstance(v,int) for v in d)
    assert all(v>=0 or state[0][i]>123*SC//128 for i,v in enumerate(d))
    upper=sum(b*v*DS for b,v in zip(params['b_numerators'],d))
    for (i,j,aw) in [r for r in params['a_upper'] if r[2]]:
        z=a.INDEX[i,j];l,u=checker.scalar.derivative_range(state[0][z],state[1][z]);s=sum(d[i:j]);upper+=aw*s*(u if s>=0 else l)
    assert upper==int(result['upper_numerator'])<0 and int(result['denominator'])==params['denominator']*DS


def main():
    start=time.monotonic();packed=(HERE/'cover-lifted-graph-replacement.input.json.gz').read_bytes();raw=gzip.decompress(packed);doc=json.loads(raw)
    snapshot=json.loads((HERE/'cover-lifted-graph-replacement-snapshot.json').read_bytes());assert sha(packed)==snapshot['input_sha256'] and sha(raw)==snapshot['uncompressed_sha256']
    assert doc['schema']=='lifted-graph-local-replacement-v1';source=doc['source'];params=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    for name,digest in source['input_sha256'].items():assert sha((ROOT/name).read_bytes())==digest,name
    checker=graph.GraphReplay(json.loads((HERE/'cover_newjet.json').read_bytes()));target=F(source['target'])*energy.g.DEN;assert target.denominator==1;target=target.numerator
    replacements={r['path']:r for r in doc['replacements']};assert len(replacements)==13
    before,ancestor_counts=graph.reconstruct(source,replacements,params,checker,target)
    old=doc['old_subtrees'];branches={r['path']:r for r in old['branches']};leaves={r['path']:r for r in old['accepted']};assert len(branches)==len(old['branches']) and len(leaves)==len(old['accepted']) and not(set(branches)&set(leaves))
    todo=[(p,before[p]) for p in replacements];seen=set();bounds=steps=0;kinds={}
    while todo:
        p,state=todo.pop();assert p not in seen;seen.add(p)
        if p in old['OBBT']:
            step=codec.unpack_obbt(state,old['OBBT'][p],target,obbt.shared.w);obbt.verify({**step,'result':None},target,checker.scalar)
            bounds+=len(step['certificates']);state=step['new_cell']
        for packedstep in old['Newton'].get(p,[]):
            assert state is not None;step=codec.unpack_newton(state,packedstep,obbt.shared.w);state=newton.verify_step(state,step,params,checker.scalar);steps+=1
        if p in leaves:
            leaf=codec.unpack_leaf(state,leaves[p],obbt.shared.w);assert leaf['path']==p and leaf['depth']==len(p)-1;kind=leaf['kind'];kinds[kind]=kinds.get(kind,0)+1
            if kind in ['sublevel_empty','stationary_empty']:assert state is None
            elif kind=='reflection':assert state is not None and state[1][8]<state[0][0]
            elif kind=='stationary':assert state is not None;stationary(state,leaf['result'],params,checker)
            else:
                assert kind=='value' and state is not None;_,_,floor=energy.minorant(state,leaf['result']['certificate']);assert floor==int(leaf['result']['floor_numerator']) and floor>=target
        else:
            assert p in branches and state is not None;b=branches[p];assert state[0][b['axis']]<b['cut']<state[1][b['axis']]
            for bit in ['0','1']:
                child=a.child(state,b['axis'],b['cut'],bit=='0');assert child is not None;todo.append((p+bit,child))
    assert seen==set(branches)|set(leaves) and set(old['OBBT'])<=seen and set(old['Newton'])<=seen
    details=[]
    for p,row in replacements.items():
        assert row['kind']=='lifted_graph' and row['depth']==len(p)-1;details.append({'path':p,**graph.verify(before[p],row['result'],params,checker)})
    expected=doc['counts'];assert len(branches)==expected['old_branches'] and len(leaves)==expected['old_leaves'] and bounds==expected['old_OBBT_bounds'] and steps==expected['old_Newton_steps']
    assert not any(name in sys.modules for name in ['numpy','scipy','networkx'])
    out={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'input_sha256':sha(packed),'all_passed':True,
      'no_site_packages':sys.flags.no_site,'optimization_libraries_imported':False,'ancestor_counts':ancestor_counts,
      'old_complete_local_nodes':len(seen),'old_branches':len(branches),'old_leaves':len(leaves),'old_leaf_kinds':kinds,
      'old_OBBT_bounds':bounds,'old_Newton_steps':steps,'replacement_graph_leaves':len(replacements),
      'nodes_saved':len(seen)-len(replacements),'payload_metrics':expected,'strict_certificates':details,
      'open_ancestor_siblings_not_claimed_covered':True,'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    (HERE/'cover-lifted-graph-replacement-replay.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
