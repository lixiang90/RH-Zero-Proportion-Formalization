"""Fetch one fixed public GitHub raw source and compare exact bytes. No proof execution."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import urllib.request

root = Path(__file__).resolve().parents[1]
here = Path(__file__).resolve().parent
commit = '7ddd0caf46037111ccda30c61be2a562fb5b8e30'
relative = 'research-goal-20261020-w9a2-delivery/draft-v8/Solution.lean'
expected = '5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b'
local = (root/relative).read_bytes()
assert len(local) == 1829382 and hashlib.sha256(local).hexdigest() == expected
url = 'https://raw.githubusercontent.com/lixiang90/RH-Zero-Proportion-Formalization/'+commit+'/'+relative
request = urllib.request.Request(url, headers={'User-Agent':'W9A2-fixed-public-source-byte-comparison'})
with urllib.request.urlopen(request, timeout=60) as response:
    raw = response.read()
    observation = {'observed_at_UTC':datetime.now(timezone.utc).isoformat(), 'URL':url,
        'effective_URL':response.url,'HTTP_status':response.status,
        'headers':{k:response.headers.get(k) for k in ('Date','ETag','Content-Length','Age','X-Cache')}}
assert observation['HTTP_status'] == 200 and raw == local
observation.update({'fixed_commit':commit,'source_path':relative,'source_bytes':len(raw),
    'source_SHA256':hashlib.sha256(raw).hexdigest(),'exact_public_bytes_equal':True,
    'full_repository_tree_audit_claimed':False,'official_acceptance_claimed':False,
    'scope':'One fixed public GitHub raw source, exact byte comparison to frozen v8. Not a fresh full tree audit or official verification.'})
out = here/'observation.json'
assert not out.exists()
out.write_bytes((json.dumps(observation,indent=2)+'\n').encode())
rows=[{'path':p.name,'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(here.iterdir()) if p.is_file() and p.name!='files.json']
(here/'files.json').write_bytes((json.dumps({'schema':'v8-fixed-public-source-sync-v1','files':rows},indent=2)+'\n').encode())
print(json.dumps(observation))
