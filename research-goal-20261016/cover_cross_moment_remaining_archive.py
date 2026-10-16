"""Freeze the stopped six-case extension and audit overlap of prior positives."""
from pathlib import Path
import gzip,hashlib,json
HERE=Path(__file__).parent;ROOT=HERE.parent
sha=lambda b:hashlib.sha256(b).hexdigest()


def minimal(paths):
    result=[]
    for p in sorted(set(paths),key=lambda p:(len(p),p)):
        if not any(p.startswith(q) for q in result):result.append(p)
    return result


def main():
    raw=(HERE/'cover-cross-moment-remaining-six.json').read_bytes();doc=json.loads(raw)
    input_raw=(HERE/'cover-curvature-parent64.input.json.gz').read_bytes();source=json.loads(gzip.decompress(input_raw))
    assert sha(input_raw)==doc['receipt']['parent64_input_sha256'] and len(doc['rows'])==6
    assert all(r['integer_certificate'] is None and r['dual_hint']['minimum_energy_slack_hint']==0 for r in doc['rows'])
    wanted={r['path'] for r in doc['rows']};needed={p[:k] for p in wanted for k in range(1,len(p))}
    projection={k:source[k] for k in ['root','target','input_sha256']}
    for key in ['branches','OBBT','Newton']:projection[key]={p:r for p,r in source[key].items() if p in needed}
    projection['cases']=[c for c in source['cases'] if c['path'] in wanted]
    archive={'schema':'cross-moment-single-midpoint-negative-six-v1','source':projection,'records':doc['rows'],
      'receipt':doc['receipt'],'provenance':{'full_batch_sha256':sha(raw),'full_parent64_input_gzip_sha256':sha(input_raw),
      'projection_keeps_all_strict_ancestor_operations':True},'new_strict_exclusions':0,
      'exact_LP_primal_feasibility_verified':False,'complete_global_cover':False,'new_zero_proportion_proven':False}
    data=(json.dumps(archive,separators=(',',':'))+'\n').encode();packed=gzip.compress(data,mtime=0)
    out=HERE/'cover-cross-moment-remaining-evidence';out.mkdir(exist_ok=True)
    (out/'proof.json.gz').write_bytes(packed)
    receipt={'schema':archive['schema'],'exporter_sha256':sha(Path(__file__).read_bytes()),'proof_gzip_sha256':sha(packed),
      'proof_gzip_bytes':len(packed),'uncompressed_sha256':sha(data),'uncompressed_bytes':len(data),
      'source_batch_sha256':sha(raw),'parent64_input_gzip_sha256':sha(input_raw),'cases':6,
      'strict_ancestor_nodes':len(needed),'strict_ancestor_branch_records':len(projection['branches']),
      'new_strict_exclusions':0,'complete_global_cover':False,'new_zero_proportion_proven':False}
    (out/'manifest.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8')
    direct_raw=(HERE/'cover-lifted-graph64.json').read_bytes();direct=json.loads(direct_raw)
    disj_raw=(HERE/'cover-lifted-graph-disjunction8.json').read_bytes();disj=json.loads(disj_raw)
    moment_raw=(HERE/'cover-cross-moment-integer-two.json').read_bytes();moment=json.loads(moment_raw)
    replay_raw=(HERE/'cover-cross-moment-independent-replay.json').read_bytes();replay=json.loads(replay_raw)
    assert replay['all_checks_passed'] and replay['local_strict_integer_contradictions']==2 and replay['input_sha256']==sha(moment_raw)
    old_direct=sorted(r['path'] for r in direct['rows'] if r['graph']);old_split=sorted(r['path'] for r in disj['rows'] if r['selected_split'])
    new=sorted(r['path'] for r in moment['rows']);assert len(old_direct)==13 and len(old_split)==1 and len(new)==2
    comparisons=[]
    for kind,paths in [('direct_graph',old_direct),('one_split_graph',old_split)]:
        for p in paths:
            for q in new:
                relation='equal' if p==q else 'old_ancestor' if q.startswith(p) else 'moment_ancestor' if p.startswith(q) else None
                if relation:comparisons.append({'old_method':kind,'old_path':p,'moment_path':q,'relation':relation})
    prior=minimal(old_direct+old_split);union=minimal(prior+new);added=[q for q in new if not any(q.startswith(p) for p in prior)]
    assert len(prior)==14 and len(union)==15 and added==['r001000001000001101011101']
    overlap={'scope':'Path-level union of independently replayed local numerical contradictions on one frozen parent64 cohort; not a global proof or an actual Lean leaf claim.',
      'script_sha256':sha(Path(__file__).read_bytes()),'sources_sha256':{'cover-lifted-graph64.json':sha(direct_raw),
      'cover-lifted-graph-disjunction8.json':sha(disj_raw),'cover-cross-moment-integer-two.json':sha(moment_raw),
      'cover-cross-moment-independent-replay.json':sha(replay_raw)},'old_direct_parent_paths':old_direct,
      'old_one_split_parent_paths':old_split,'new_moment_parent_paths':new,'overlaps':comparisons,
      'old_union_non_nested_regions':len(prior),'union_non_nested_regions':len(union),'new_distinct_regions':len(added),
      'new_distinct_parent_paths':added,'remaining_six_new_regions':0,'actual_Lean_union_instantiated':False,
      'complete_global_cover':False,'new_zero_proportion_proven':False}
    op=HERE/'cover-cross-moment-overlap.json';op.write_text(json.dumps(overlap,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'archive':receipt,'overlap_sha256':sha(op.read_bytes()),'new_distinct_regions':len(added),'overlaps':comparisons}),flush=True)
if __name__=='__main__':main()
