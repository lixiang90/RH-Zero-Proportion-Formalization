"""Freeze the completed lifted-graph eight-parent pilot only."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).parent;ROOT=HERE.parent
FILES=['cover_lifted_graph_probe.py','cover_curvature_parent_probe.py','cover_lifted_graph_verify.py',
 'cover_lifted_graph_archive.py','cover_lifted_graph_archive_replay.py','cover-lifted-graph8.json','cover-lifted-graph8-replay.json',
 'cover-lifted-graph8-evidence/proof.json.gz','cover-lifted-graph8-evidence/manifest.json','cover-lifted-graph8-evidence/independent-replay.json',
 'cover_lifted_graph8_note.md','cover_lifted_graph8_manifest.py']
def main():
    rows=[]
    for name in FILES:
        p=HERE/name;b=p.read_bytes();rows.append({'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
    out={'scope':'Immutable local lifted derivative-graph pilot, eight fixed parents, four strict exclusions.',
      'files':rows,'file_count':len(rows),'total_bytes':sum(r['bytes'] for r in rows),'independent_standalone_replay_passed':True,
      'complete_global_cover':False,'actual_lifted_graph_Lean_consumer_complete':False,'new_zero_proportion_proven':False}
    target=HERE/'cover-lifted-graph8-files.json';target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'manifest':str(target),'sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'files':len(rows),'bytes':out['total_bytes']}))
if __name__=='__main__':main()
