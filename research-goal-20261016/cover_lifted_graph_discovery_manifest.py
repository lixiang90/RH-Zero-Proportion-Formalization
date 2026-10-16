"""Pin only the fixed graph discovery cohort and small reproducibility helpers."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).parent;ROOT=HERE.parent
FILES=['cover-curvature-parent64.input.json.gz','cover-curvature-parent64-snapshot.json','cover_curvature_parent_sample.py',
 'cover-lifted-graph-selection8.json','cover_lifted_graph_recompute.py','cover_lifted_graph_discovery_input_note.md','cover_lifted_graph_discovery_manifest.py']
def main():
    rows=[]
    for name in FILES:
        p=HERE/name;b=p.read_bytes();rows.append({'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
    out={'scope':'Minimal fixed parent64 graph discovery inputs; excludes the large negative-experiment proof bundle.',
      'files':rows,'file_count':len(rows),'total_bytes':sum(r['bytes'] for r in rows),'large_original_checkpoint_required_for_replay':False,
      'complete_global_cover':False,'new_zero_proportion_proven':False}
    p=HERE/'cover-lifted-graph-discovery-input-files.json';p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'manifest':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'files':len(rows),'bytes':out['total_bytes']}))
if __name__=='__main__':main()
