"""One-level exact graph disjunction on the same eight residual parents.

LP scalar/actual-derivative disagreement selects at most three span axes.
Only one split level is tested.  All children use the frozen graph and old
single-slab predicates; parent closure requires both exact child proofs.
The existing value-based split rule provides a same-depth control.
"""
from pathlib import Path
import gzip,hashlib,json,math,time
import numpy as np
import cover_lifted_graph_probe as graph
g=graph.g;SC=graph.SC;DS=graph.DS;HERE=Path(__file__).parent
sha=lambda b:hashlib.sha256(b).hexdigest()


def main():
    start=time.monotonic();packed=(HERE/'cover-curvature-parent64.input.json.gz').read_bytes();source=json.loads(gzip.decompress(packed));cases={r['path']:r for r in source['cases']}
    selectionraw=(HERE/'cover-lifted-graph-energy8.json').read_bytes();selection=json.loads(selectionraw);assert selection['receipt']['input_sha256']==sha(packed)
    taylor=graph.context.curvature.first.TaylorOracle(HERE/'cover_newjet.json');oracle=graph.GraphOracle(HERE/'cover_newjet.json');rows=[]
    counts={'parents':0,'candidate_splits':0,'exact_graph_child_closures':0,'exact_old_child_closures':0,'graph_parent_closures':0,
      'old_slab_parent_closures_at_same_split':0,'old_rule_graph_parent_closures':0,'old_rule_old_parent_closures':0,'new_over_old_rule_graph':0}
    cache={}
    def child_trial(state):
        key=tuple(state[0])+tuple(state[1])
        if key not in cache:
            old,os,_=graph.solve(state,taylor,oracle,False);new,ns,_=graph.solve(state,taylor,oracle,True)
            cache[key]={'cell':state,'old':old,'graph':new,'old_statistics':os,'graph_statistics':ns}
        return cache[key]
    def split_trial(state,axis,cut,origin):
        children=[]
        for upper in [True,False]:
            child=g.split(state,axis,cut,upper);assert child is not None
            children.append(child_trial(child))
        return {'axis':axis,'cut':cut,'origin':origin,'children':children,'graph_closed':all(c['graph'] for c in children),'old_closed':all(c['old'] for c in children)}
    for selected in selection['rows']:
        path=selected['path'];state=tuple(cases[path]['before']);base,stats,lp=graph.solve(state,taylor,oracle,True);assert base is None and lp.success and lp.fun<=1e-10
        disagreements=[]
        for t,(i,j,aw) in enumerate(g.TERMS):
            x=float(sum(lp.x[i:j]));P=round(2*SC*x);v,_=taylor.point(P);actual=float((v.l+v.u)/2);error=abs(float(lp.x[9+t])-actual)
            disagreements.append({'term':t,'axis':g.LOOK[i,j],'x_hint':x,'u_hint':float(lp.x[9+t]),'actual_wprime_hint':actual,
              'error_hint':error,'weighted_error_hint':error*math.sqrt(aw/g.D)})
        choices=sorted(disagreements,key=lambda r:r['weighted_error_hint'],reverse=True)[:3]
        rec=graph.context.w.certify(state);axis,cut=g.cut(state,rec);assert state[0][axis]<cut<state[1][axis]
        control=split_trial(state,axis,cut,'old_value_rule_before_OBBT');counts['old_rule_graph_parent_closures']+=control['graph_closed'];counts['old_rule_old_parent_closures']+=control['old_closed']
        candidates=[];seen=set();chosen=None
        for hint in choices:
            z=hint['axis'];x=hint['x_hint'];cuts=[(round(x*SC),'LP_disagreement_point'),(round(x)*SC,'nearest_integer'),(round(2*x)*SC//2,'nearest_half_integer')]
            for q,origin in cuts:
                if not state[0][z]<q<state[1][z] or (z,q) in seen:continue
                seen.add((z,q));trial=split_trial(state,z,q,origin);trial['selection_hint']=hint;candidates.append(trial);counts['candidate_splits']+=1
                counts['exact_graph_child_closures']+=sum(bool(c['graph']) for c in trial['children']);counts['exact_old_child_closures']+=sum(bool(c['old']) for c in trial['children'])
                if trial['graph_closed']:chosen=trial;break
            if chosen:break
        counts['parents']+=1;counts['graph_parent_closures']+=bool(chosen)
        counts['old_slab_parent_closures_at_same_split']+=bool(chosen and chosen['old_closed']);counts['new_over_old_rule_graph']+=bool(chosen and not control['graph_closed'])
        rows.append({'path':path,'top3_disagreement_hints':choices,'old_rule':control,'trials':candidates,'selected_split':None if chosen is None else {'axis':chosen['axis'],'cut':chosen['cut']}})
        print(json.dumps({**counts,'seconds':time.monotonic()-start}),flush=True)
    out={'receipt':{'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'engine_sha256':sha(Path(graph.__file__).read_bytes()),
      'input_sha256':sha(packed),'selection_sha256':sha(selectionraw),'table_sha256':oracle.sha,'target':'11/1250','counts':counts,'unique_child_LPs':len(cache),
      'maximum_split_depth':1,'independent_replay_passed':False,'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start},'rows':rows}
    (HERE/'cover-lifted-graph-disjunction8.json').write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(out['receipt']),flush=True)
if __name__=='__main__':main()
