"""Explicit read-only public HTTP evidence fetch. No proof/math execution."""
import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import time
import urllib.error
import urllib.request
HERE=Path(__file__).resolve().parent
def save(p,b):
    with p.open('xb') as f:f.write(b);f.flush();os.fsync(f.fileno())
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--name',required=True);ap.add_argument('--url',required=True);a=ap.parse_args()
    assert all(c.isalnum() or c in '-_' for c in a.name)
    assert a.url.startswith(('https://www.riemannzeta.fun/','https://api.github.com/repos/josusanmartin/riemann/','https://raw.githubusercontent.com/josusanmartin/riemann/'))
    suffix='&' if '?' in a.url else '?';url=a.url+suffix+'independent_fresh='+str(time.time_ns())
    headers={'User-Agent':'RH-Zero-Independent-ReadOnly-Audit','Accept':'application/json, text/html, text/plain;q=0.9',
        'Cache-Control':'no-cache, no-store, max-age=0','Pragma':'no-cache'}
    start=datetime.now(timezone.utc).isoformat();req=urllib.request.Request(url,headers=headers,method='GET')
    try:
        with urllib.request.urlopen(req,timeout=45) as response:
            body=response.read();meta={'requested_url':url,'final_url':response.url,'http_status':response.status,
                'request_headers':headers,'response_headers':dict(response.headers.items()),
                'request_UTC':start,'completed_UTC':datetime.now(timezone.utc).isoformat(),
                'body_file':a.name+'.body','body_bytes':len(body),'body_sha256':sha256(body).hexdigest(),
                'source_executed':False,'retries':0}
        save(HERE/(a.name+'.body'),body)
        save(HERE/(a.name+'.receipt.json'),(json.dumps(meta,indent=2)+'\n').encode('utf8'))
        print(json.dumps({'name':a.name,'HTTP':meta['http_status'],'UTC':meta['completed_UTC'],
            'Age':meta['response_headers'].get('Age'),'Cache':meta['response_headers'].get('X-Vercel-Cache'),
            'bytes':len(body),'sha256':meta['body_sha256']}))
    except BaseException as exc:
        save(HERE/(a.name+'.failure.json'),(json.dumps({'url':url,'UTC':datetime.now(timezone.utc).isoformat(),
            'error':repr(exc),'retries':0})+'\n').encode('utf8'));raise
if __name__=='__main__':main()
