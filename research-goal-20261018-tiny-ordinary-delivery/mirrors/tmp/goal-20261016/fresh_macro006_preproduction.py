from pathlib import Path
from fractions import Fraction
from urllib.request import Request, urlopen
import datetime, hashlib, json, time
p=Path(__file__).with_name('macro006-preproduction-fresh-record.json')
assert not p.exists()
u='https://www.riemannzeta.fun/api/leaderboard?macro006_preproduction='+str(time.time_ns())
q=Request(u,headers={'User-Agent':'RH-Zero-research-fresh-check','Cache-Control':'no-cache, no-store'})
with urlopen(q,timeout=40) as r:
 b=r.read(1000001);assert len(b)<=1000000 and r.status==200
 h={k:r.headers.get(k) for k in ['Date','Age','X-Vercel-Cache','Cache-Control','ETag']}
 j=json.loads(b);x=j['current']['exactRational'];R=Fraction(int(x['numerator']),int(x['denominator']))
 c=Fraction(3337839448633819172184136761695440236797,4955319193827760237900000000000000000000)
 o={'UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':u,'status':r.status,'headers':h,'body_sha256':hashlib.sha256(b).hexdigest(),'record_R':str(R),'ordinary_proved_tiny_candidate':str(c),'tiny_strictly_above_current':c>R,'current':j['current']}
 with p.open('x',encoding='utf8') as f:json.dump(o,f,indent=2);f.write('\n')
 print(json.dumps({k:o[k] for k in ['UTC','status','headers','record_R','tiny_strictly_above_current']}))
