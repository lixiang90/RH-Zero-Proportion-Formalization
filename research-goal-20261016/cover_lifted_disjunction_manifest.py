"""Pin the complete one-level pilot and its tiny standalone positive archive."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).parent;ROOT=HERE.parent
FILES=['cover_lifted_graph_disjunction.py','cover-lifted-graph-disjunction8.json.gz','cover_lifted_graph_disjunction_verify.py',
 'cover-lifted-graph-disjunction8-replay.json','cover_lifted_graph_disjunction_archive.py','cover_lifted_graph_disjunction_archive_replay.py',
 'cover-lifted-disjunction-evidence/proof.json.gz','cover-lifted-disjunction-evidence/manifest.json','cover-lifted-disjunction-evidence/independent-replay.json',
 'cover_lifted_disjunction_note.md','cover_lifted_disjunction_manifest.py']
def main():
    rows=[]
    for name in FILES:
        p=HERE/name;b=p.read_bytes();rows.append({'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
    out={'scope':'One extra parent region by one split/two strict graph leaves, fixed eight residual cells.',
      'files':rows,'file_count':len(rows),'total_bytes':sum(r['bytes'] for r in rows),'independent_python_no_site_replay_passed':True,
      'complete_global_cover':False,'new_zero_proportion_proven':False}
    p=HERE/'cover-lifted-disjunction-files.json';p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'manifest':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'files':len(rows),'bytes':out['total_bytes']}))
if __name__=='__main__':main()
