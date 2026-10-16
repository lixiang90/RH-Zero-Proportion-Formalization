"""Independent python -S replay of the fixed one-level graph disjunctions."""
from pathlib import Path
from fractions import Fraction as F
import gzip,hashlib,json,sys,time
import cover_exact_scalar_replay as scalar_adapter
scalar_adapter.install()
import cover_lifted_graph_verify as graph
import cover_compact_codec as codec
import cover_sublevel_obbt_verify as obbt
HERE=Path(__file__).parent;ROOT=HERE.parent;a=graph.a
sha=lambda b:hashlib.sha256(b).hexdigest()

def main():
    start=time.monotonic();path=HERE/'cover-lifted-graph-disjunction8.json'
    if not path.exists():path=path.with_suffix('.json.gz')
    container=path.read_bytes();raw=gzip.decompress(container) if path.suffix=='.gz' else container;proof=json.loads(raw)
    packed=(HERE/'cover-curvature-parent64.input.json.gz').read_bytes();assert sha(packed)==proof['receipt']['input_sha256'];source=json.loads(gzip.decompress(packed))
    for name,digest in source['input_sha256'].items():assert sha((ROOT/name).read_bytes())==digest,name
    tabraw=(HERE/'cover_newjet.json').read_bytes();assert sha(tabraw)==proof['receipt']['table_sha256'];checker=graph.GraphReplay(json.loads(tabraw))
    params=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes());target=F(source['target'])*obbt.shared.g.DEN;assert target.denominator==1;target=target.numerator
    selected={r['path'] for r in proof['rows']};assert len(selected)==8;before,ancestors=graph.reconstruct(source,selected,params,checker,target)
    graph64=json.loads((HERE/'cover-lifted-graph64.json').read_bytes());old_positive={r['path'] for r in graph64['rows'] if r['graph']};assert not selected&old_positive
    seen_cert=set();details=[];parents=[];candidate_splits=0;newoldcounts={'graph':0,'old':0};sourcecases={r['path']:r for r in source['cases']};work={k:0 for k in source['cases'][0]['recorded_old_work']}
    for row in proof['rows']:
        parent=before[row['path']];success=[]
        for label,trial in [('old_rule',row['old_rule'])]+[('candidate',q) for q in row['trials']]:
            axis,cut=trial['axis'],trial['cut'];assert 0<=axis<45 and parent[0][axis]<cut<parent[1][axis]
            assert len(trial['children'])==2
            for k,child in enumerate(trial['children']):
                expected=a.child(parent,axis,cut,k==0);assert expected is not None and child['cell']==[list(v) for v in expected]
                for method in ['old','graph']:
                    cert=child[method]
                    if cert:
                        key=(codec.digest(expected),codec.digest(cert))
                        if key not in seen_cert:
                            seen_cert.add(key);details.append({'path':row['path'],'axis':axis,'cut':cut,'child':k,'method':method,**graph.verify(expected,cert,params,checker)})
                        if label=='candidate':newoldcounts[method]+=1
            assert trial['graph_closed']==all(c['graph'] is not None for c in trial['children'])
            assert trial['old_closed']==all(c['old'] is not None for c in trial['children'])
            if label=='candidate':
                candidate_splits+=1
                if trial['graph_closed']:success.append({'axis':axis,'cut':cut})
        assert row['selected_split']==(success[0] if success else None)
        if success:
            assert not row['old_rule']['graph_closed'] and not row['old_rule']['old_closed'];parents.append(row['path'])
            for k,v in sourcecases[row['path']]['recorded_old_work'].items():work[k]+=v
    counts=proof['receipt']['counts'];assert candidate_splits==counts['candidate_splits'] and len(parents)==counts['graph_parent_closures']
    assert newoldcounts['graph']==counts['exact_graph_child_closures'] and newoldcounts['old']==counts['exact_old_child_closures']
    assert not any(name in sys.modules for name in ['numpy','scipy','networkx'])
    out={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'input_sha256':sha(raw),'all_passed':True,'no_site_packages':sys.flags.no_site,
      'parents':8,'ancestor_counts':ancestors,'candidate_splits':candidate_splits,'unique_exact_certificates':len(details),
      'strict_parent_closures':len(parents),'strict_parent_paths':parents,'distinct_from_original13':True,
      'candidate_child_proof_occurrences':newoldcounts,'source_recorded_work_under_new_parents':work,
      'single_child_occurrences_are_not_additional_whole_parents':True,'LP_negative_controls_are_diagnostic_only':True,
      'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    (HERE/'cover-lifted-graph-disjunction8-replay.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
