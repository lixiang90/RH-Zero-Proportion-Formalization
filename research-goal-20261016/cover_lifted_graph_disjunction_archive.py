"""Project the one successful one-level graph disjunction to strict ancestors."""
from pathlib import Path
import gzip,hashlib,json
HERE=Path(__file__).parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
    raw=(HERE/'cover-lifted-graph-disjunction8.json').read_bytes();proof=json.loads(raw);packed=(HERE/'cover-curvature-parent64.input.json.gz').read_bytes();source=json.loads(gzip.decompress(packed));assert sha(packed)==proof['receipt']['input_sha256']
    selected=[r for r in proof['rows'] if r['selected_split']];wanted={r['path'] for r in selected};assert len(wanted)==1
    needed={p[:k] for p in wanted for k in range(1,len(p))};projection={k:source[k] for k in ['root','target','input_sha256']}
    for key in ['branches','OBBT','Newton']:projection[key]={p:r for p,r in source[key].items() if p in needed}
    projection['cases']=[r for r in source['cases'] if r['path'] in wanted];controls=json.loads((HERE/'cover-curvature-parent64.json').read_bytes())
    records=[]
    for row in selected:
        s=row['selected_split'];trial=next(t for t in row['trials'] if t['axis']==s['axis'] and t['cut']==s['cut']);assert trial['graph_closed']
        records.append({'path':row['path'],'axis':s['axis'],'cut':s['cut'],'children':[c['graph'] for c in trial['children']],
          'old_single_slab_children':[c['old'] for c in trial['children']],'old_rule':{'axis':row['old_rule']['axis'],'cut':row['old_rule']['cut'],
            'graph_closed':row['old_rule']['graph_closed'],'old_closed':row['old_rule']['old_closed']},'selection_hint':trial['selection_hint']})
    graph64raw=(HERE/'cover-lifted-graph64.json').read_bytes();graph64=json.loads(graph64raw)
    out={'schema':'lifted-graph-disjunction-projection-v1','source':projection,'records':records,
      'controls':[{'path':r['path'],'control':r['control']} for r in controls['rows'] if r['path'] in wanted],
      'previous_graph_parent_paths':[r['path'] for r in graph64['rows'] if r['graph']],
      'source_recorded_descendant_branches':[r for r in source['source_descendant_branches'] if any(r['path'].startswith(p) for p in wanted)],
      'provenance':{'full_disjunction_proof_sha256':sha(raw),'parent64_input_gzip_sha256':sha(packed),'prior_graph64_sha256':sha(graph64raw)},
      'complete_global_cover':False,'new_zero_proportion_proven':False}
    data=(json.dumps(out,separators=(',',':'))+'\n').encode();compressed=gzip.compress(data,mtime=0);target=HERE/'cover-lifted-disjunction-evidence';target.mkdir(exist_ok=True)
    (target/'proof.json.gz').write_bytes(compressed);receipt={'schema':out['schema'],'exporter_sha256':sha(Path(__file__).read_bytes()),'proof_gzip_sha256':sha(compressed),
      'proof_gzip_bytes':len(compressed),'uncompressed_sha256':sha(data),'uncompressed_bytes':len(data),'parent_closures':1,'split_nodes':1,'graph_leaves':2,
      'strict_ancestor_branches':len(needed),'complete_global_cover':False,'new_zero_proportion_proven':False}
    (target/'manifest.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
