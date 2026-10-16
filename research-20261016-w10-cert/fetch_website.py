"""Archive the fixed current-record contract and statement templates."""
from pathlib import Path
import hashlib,json,urllib.request
OUT=Path(__file__).with_name('website-snapshot')
COMMIT='9e6ca6615b9dbfec4a1d722995cff0ffe3abf9bb'
FILES=['challenge/contract.json','data/live-records.json','live-head.json',
 'challenge/templates/CandidateSpec.lean.tmpl','challenge/templates/Challenge.Candidate.lean']
def main():
  result={}
  tree=json.loads(urllib.request.urlopen(f'https://api.github.com/repos/josusanmartin/riemann/git/trees/{COMMIT}?recursive=1',timeout=60).read())
  candidates=[x['path'] for x in tree['tree'] if any(y in x['path'] for y in ['live-record','live-head','CandidateSpec.lean','Challenge.Candidate.lean','contract.json'])]
  (OUT/'tree-paths.json').write_text(json.dumps(candidates,indent=2)+'\n')
  print(json.dumps(candidates),flush=True)
  record_files=[x['path'] for x in tree['tree'] if x['type']=='blob' and x['path'].startswith('submissions/attempt-024/') and not x['path'].endswith('.lean') and x.get('size',0)<256000]
  print(json.dumps(record_files),flush=True)
  for name in FILES+record_files:
    url=f'https://raw.githubusercontent.com/josusanmartin/riemann/{COMMIT}/{name}'
    try:raw=urllib.request.urlopen(url,timeout=60).read()
    except urllib.error.HTTPError as e:
      if e.code==404:result[name]={'missing':True};continue
      raise
    p=OUT/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
    result[name]={'url':url,'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}
  (OUT/'provenance.json').write_text(json.dumps({'commit':COMMIT,'files':result},indent=2)+'\n',encoding='utf8')
  print(json.dumps(result))
if __name__=='__main__':main()
