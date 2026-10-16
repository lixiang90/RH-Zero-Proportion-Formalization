"""Freeze the completed thirteen-witness parent64 graph expansion."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).parent;ROOT=HERE.parent
FILES=['cover_lifted_graph64_probe.py','cover-lifted-graph64.json','cover-lifted-graph64-replay.json',
 'cover-lifted-graph64-evidence/proof.json.gz','cover-lifted-graph64-evidence/manifest.json','cover-lifted-graph64-evidence/independent-replay.json',
 'cover_lifted_graph_pilot.py','cover-lifted-graph-pilot.json','cover_lifted_graph64_note.md','cover_lifted_graph64_manifest.py']
def main():
    dependency=HERE/'cover-lifted-graph8-files.json';dr=dependency.read_bytes();dep=json.loads(dr)
    for row in dep['files']:assert hashlib.sha256((ROOT/row['path']).read_bytes()).hexdigest()==row['sha256'],row['path']
    rows=[]
    for name in FILES:
        p=HERE/name;b=p.read_bytes();rows.append({'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
    out={'scope':'Immutable local lifted derivative-graph expansion: 13 of the same 64 fixed parents, including graph8 positives.',
      'dependency_manifest':dependency.relative_to(ROOT).as_posix(),'dependency_manifest_sha256':hashlib.sha256(dr).hexdigest(),
      'files':rows,'file_count':len(rows),'total_bytes':sum(r['bytes'] for r in rows),'independent_standalone_replay_passed':True,
      'complete_global_cover':False,'actual_lifted_graph_Lean_consumer_complete':False,'new_zero_proportion_proven':False}
    target=HERE/'cover-lifted-graph64-files.json';target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'manifest':str(target),'sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'files':len(rows),'bytes':out['total_bytes']}))
if __name__=='__main__':main()
