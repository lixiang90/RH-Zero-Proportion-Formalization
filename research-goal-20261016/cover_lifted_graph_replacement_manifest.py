"""Freeze the checked thirteen-subtree replacement, API, and tiny negative pilot."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).parent;ROOT=HERE.parent
FILES=['cover_lifted_graph_api.py','cover-lifted-graph-api-replay.json','cover_lifted_graph_projection.py',
 'cover-lifted-graph-replacement.input.json.gz','cover-lifted-graph-replacement-snapshot.json',
 'cover_exact_scalar_replay.py','cover_lifted_graph_replacement_verify.py','cover-lifted-graph-replacement-replay.json',
 'cover_lifted_graph_integration_note.md','cover_lifted_graph_energy_probe.py','cover-lifted-graph-energy8.json',
 'cover_lifted_graph_energy_note.md','cover_lifted_graph_replacement_manifest.py']
def main():
    rows=[]
    for name in FILES:
        p=HERE/name;b=p.read_bytes();rows.append({'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
    out={'scope':'Exact complete-local-subtree replacement by13 graph leaves; stable API and stopped negative energy pilot.',
      'files':rows,'file_count':len(rows),'total_bytes':sum(r['bytes'] for r in rows),'independent_python_no_site_replay_passed':True,
      'complete_global_cover':False,'new_zero_proportion_proven':False}
    p=HERE/'cover-lifted-graph-replacement-files.json';p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'manifest':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'files':len(rows),'bytes':out['total_bytes']}))
if __name__=='__main__':main()
