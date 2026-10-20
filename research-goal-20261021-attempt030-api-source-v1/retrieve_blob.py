"""Follow the observed Git blob link: Contents response omits >1MB content.
The failed two-file helper is retained. One blob GET, no retry/redirect/auth.
"""
from pathlib import Path
import base64, hashlib, json, time, urllib.request
ROOT=Path(__file__).resolve().parent
metadata=json.loads((ROOT/'Solution.lean.api.raw.json').read_bytes())
assert metadata['encoding']=='none' and metadata['content']==''
assert metadata['size']==1798336 and metadata['sha']=='c6fd5f56c248f880f733008c96e659fc1dd1b4a2'
url=metadata['git_url']
assert url=='https://api.github.com/repos/josusanmartin/riemann/git/blobs/c6fd5f56c248f880f733008c96e659fc1dd1b4a2'
class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self,*args,**kwargs): return None
start=time.monotonic()
receipt={'schema':'observed-public-blob-followup-v1','url':url,'reason':'Observed Contents API file metadata encoding none; follow its git_url, not retry missing base64','GET_calls':1,'retry_count':0,'proof_executed':False,'complete':False}
assert not (ROOT/'blob-receipt.json').exists()
try:
    request=urllib.request.Request(url,headers={'User-Agent':'RH-source-static-inspection','Accept':'application/vnd.github+json'})
    with urllib.request.build_opener(NoRedirect()).open(request,timeout=30) as response:
        receipt.update(status=response.status,headers=[(str(k),str(v)) for k,v in response.headers.items()])
        raw=response.read(3000001)
        with (ROOT/'Solution.lean.blob.raw.json').open('xb') as f: f.write(raw)
        receipt.update(raw_bytes=len(raw),raw_sha256=hashlib.sha256(raw).hexdigest())
        assert response.status==200 and len(raw)<=3000000
    j=json.loads(raw)
    assert j['sha']==metadata['sha'] and j['size']==metadata['size'] and j['encoding']=='base64'
    data=base64.b64decode(''.join(j['content'].split()),validate=True)
    assert len(data)==metadata['size']
    blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    assert blob==metadata['sha']
    with (ROOT/'Solution.lean').open('xb') as f: f.write(data)
    receipt.update(decoded_bytes=len(data),decoded_sha256=hashlib.sha256(data).hexdigest(),git_blob_sha1=blob)
    assert time.monotonic()-start<30
    receipt['complete']=True
except BaseException as e:
    receipt['error']={'type':type(e).__name__,'message':str(e)}
    raise
finally:
    receipt['elapsed_seconds']=time.monotonic()-start
    (ROOT/'blob-receipt.json').write_bytes((json.dumps(receipt,indent=2)+'\n').encode())
    print(json.dumps({k:v for k,v in receipt.items() if k!='headers'}))
