"""Explicit alternative endpoint after raw-host pre-request connection reset.
Two fixed anonymous public reads; no retry, redirects or proof execution.
"""
from pathlib import Path
import base64, hashlib, json, time, urllib.request

BASE = Path(__file__).resolve().parent
REF = '94954faf2713ae9628d6fbca0ae24fe64370507c'
FILES = [('submission.json', 'submissions/attempt-030/submission.json', 100000),
         ('Solution.lean', 'submissions/attempt-030/proof/Solution.lean', 2000000)]

class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        return None

def main():
    start = time.monotonic()
    receipt = {'schema': 'fixed-public-upstream-source-api-v1', 'ref': REF,
               'alternative_reason': 'Raw host connection reset before request; separate explicit root-selected API read, not automatic retry',
               'retry_count': 0, 'authenticated': False, 'files': [],
               'proof_executed': False, 'complete': False}
    output = BASE/'receipt.json'
    assert not output.exists()
    opener = urllib.request.build_opener(NoRedirect())
    try:
        for name, remote, limit in FILES:
            raw_path = BASE/(name+'.api.raw.json')
            decoded_path = BASE/name
            assert not raw_path.exists() and not decoded_path.exists()
            url = 'https://api.github.com/repos/josusanmartin/riemann/contents/'+remote+'?ref='+REF
            item = {'url': url, 'GET_calls': 0}
            receipt['files'].append(item)
            request = urllib.request.Request(url, headers={'User-Agent': 'RH-source-static-inspection', 'Accept': 'application/vnd.github+json'})
            item['GET_calls'] = 1
            with opener.open(request, timeout=max(1,30-(time.monotonic()-start))) as response:
                item['status'] = response.status
                item['headers'] = [(str(k),str(v)) for k,v in response.headers.items()]
                with raw_path.open('xb') as target:
                    raw = response.read(3000001)
                    target.write(raw)
                    target.flush()
                item['raw_bytes'] = len(raw)
                item['raw_sha256'] = hashlib.sha256(raw).hexdigest()
                assert response.status == 200 and len(raw) <= 3000000
            j = json.loads(raw)
            assert j['type'] == 'file' and j['path'] == remote and j['encoding'] == 'base64'
            data = base64.b64decode(''.join(j['content'].split()), validate=True)
            assert 0 < len(data) <= limit and len(data) == j['size']
            blob = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
            assert blob == j['sha']
            with decoded_path.open('xb') as target:
                target.write(data)
                target.flush()
            item.update(decoded_bytes=len(data), decoded_sha256=hashlib.sha256(data).hexdigest(), git_blob_sha1=blob)
            assert time.monotonic()-start < 30
        receipt['complete'] = True
    except BaseException as error:
        receipt['error'] = {'type': type(error).__name__, 'message': str(error)}
        raise
    finally:
        receipt['elapsed_seconds'] = time.monotonic()-start
        output.write_bytes((json.dumps(receipt,ensure_ascii=True,indent=2)+'\n').encode())
        print(json.dumps({'complete': receipt['complete'], 'elapsed': receipt['elapsed_seconds'],
                          'files': [{k:v for k,v in item.items() if k not in ('headers','url')} for item in receipt['files']]}))

if __name__ == '__main__':
    main()
