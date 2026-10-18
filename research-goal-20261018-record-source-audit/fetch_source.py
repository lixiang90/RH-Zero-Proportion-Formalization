"""Fetch the specified immutable public Lean source as bytes; never execute it."""
from pathlib import Path
import datetime, hashlib, json, urllib.request

HERE=Path(__file__).resolve().parent
COMMIT='cfc7ce6113199b7d5f262812d81089778e84335c'
UPSTREAM='submissions/critical-strip-exclusion-attempt-1/proof/Solution.lean'
URL=f'https://raw.githubusercontent.com/josusanmartin/riemann/{COMMIT}/{UPSTREAM}'
dest=HERE/'snapshot'/'Solution.lean'
assert not dest.exists()
request=urllib.request.Request(URL,headers={'User-Agent':'RH-Zero-static-source-audit/1'})
with urllib.request.urlopen(request,timeout=45)as response:
    raw=response.read(4_000_001)
    assert len(raw)<=4_000_000
    status=response.status
    final_url=response.geturl()
    headers={k:response.headers.get(k)for k in ['ETag','Content-Type','Content-Length','Last-Modified']}
assert status==200 and final_url==URL
raw.decode('utf-8')
dest.parent.mkdir(exist_ok=True)
with dest.open('xb')as f:f.write(raw)
receipt={'scope':'Immutable public source byte acquisition only; no Lean or certificate replay.',
         'commit':COMMIT,'upstream_path':UPSTREAM,'url':URL,'final_url':final_url,
         'retrieved_UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'status':status,'response_headers':headers,
         'path':'snapshot/Solution.lean','bytes':len(raw),
         'sha256':hashlib.sha256(raw).hexdigest(),
         'copyright_license_preserved':True,'bytes_normalized':False,
         'source_executed':False,'Lean_invocations':0,'leaf_payload_decoded':False,
         'fetcher_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
with(HERE/'fetch-receipt.json').open('x',encoding='utf-8',newline='\n')as f:
    json.dump(receipt,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps(receipt,ensure_ascii=False))
