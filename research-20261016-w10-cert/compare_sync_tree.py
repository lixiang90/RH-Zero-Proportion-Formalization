"""Read-only compare of a prepared GitHub tree and the staged local tree."""
from pathlib import Path
import argparse,json,subprocess,urllib.request
ROOT=Path(__file__).resolve().parents[1]
def main():
 ap=argparse.ArgumentParser();ap.add_argument('remote_tree')
 ap.add_argument('--staged',type=Path,default=ROOT/'tmp/w10-final-sync/staged.json');args=ap.parse_args()
 stage=json.loads(args.staged.read_text())
 rows=subprocess.check_output(['git','ls-tree','-r','-z',stage['tree']],cwd=ROOT).split(b'\0')
 local={}
 for row in rows:
  if row:
   head,name=row.split(b'\t');mode,kind,sha=head.decode().split();local[name.decode()]={'mode':mode,'sha':sha,'type':kind}
 url=f'https://api.github.com/repos/lixiang90/RH-Zero-Proportion-Formalization/git/trees/{args.remote_tree}?recursive=1'
 doc=json.loads(urllib.request.urlopen(url,timeout=60).read());assert not doc.get('truncated')
 remote={r['path']:{k:r[k] for k in ['mode','sha','type']} for r in doc['tree'] if r['type']!='tree'}
 diffs=[{'path':p,'local':local.get(p),'remote':remote.get(p)} for p in sorted(set(local)|set(remote)) if local.get(p)!=remote.get(p)]
 (args.staged.parent/'tree-comparison.json').write_text(json.dumps(diffs,indent=2)+'\n')
 print(json.dumps({'local':stage['tree'],'remote':args.remote_tree,'differences':diffs[:8],'difference_count':len(diffs)}))
if __name__=='__main__':main()
