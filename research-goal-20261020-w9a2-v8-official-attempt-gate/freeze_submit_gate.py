"""Root final delivery-byte check, without any proof replay or website mutation."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json
root=Path(__file__).resolve().parents[1]
here=Path(__file__).resolve().parent
def sha(b): return hashlib.sha256(b).hexdigest()
def pin(p):
 b=p.read_bytes()
 return {'path':p.relative_to(root).as_posix(),'bytes':len(b),'sha256':sha(b)}
refs=[
 ('research-goal-20261016/macro-reviews/012-20261020.zh.md','fb7516e57e8fe56802d16b088178c29215d10161a10060a1e007e2b7a9274347'),
 ('submission/w9a2-weighted-potential-20261020-attempt-v8/files.json','9d1778957268433a646104108620bfcef2ac999b8630cf378da5d27683e883fa'),
 ('research-goal-20261020-w9a2-attempt-v8-materials-independent/files.json','766e213ca04dd9bb1c017f059ba9f7b7435964dcf9ebb316ed22990182748bb1')]
bound=[]
for name,h in refs:
 p=root/name
 assert sha(p.read_bytes())==h,name
 bound.append(pin(p))
 if p.name=='files.json':
  for row in json.loads(p.read_bytes())['files']:
   q=p.parent/row['path']
   b=q.read_bytes()
   assert len(b)==row['bytes'] and sha(b)==row['sha256'],str(q)
packet=root/'submission/w9a2-weighted-potential-20261020-attempt-v8'
source=(packet/'proof/Solution.lean').read_bytes()
server=(packet/'submission.draft.json').read_bytes()
assert len(source)==1829382 and sha(source)=='5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b'
assert sha(server)=='d88b70050b2a1e1a69d2e1044bcc6a3d1a75c56ab8342f8559f77fe9b270362a'
wire=sha(b'submission.json\0'+server+b'proof/Solution.lean\0'+source)
assert wire=='fb457eecc550ce09bee528294dfff90137631c08e95fa26ffba1e99ec4e11bd4'
m=json.loads(server)
boundary=json.loads((here/'browser-pre-submit-boundary.json').read_bytes())
u=boundary['ui'];f=u['fields']
assert u['url']=='https://www.riemannzeta.fun/submit' and u['authenticated']=='Authenticated as @lixiang90'
assert u['quota']=='1 of 3 uploads remaining today' and boundary['active']['status']=='none'
assert u['uploadedBytes']=='1,829,382 / 2,000,000 bytes' and u['submitEnabled'] is True and f['acceptLicense'] is True
assert f['id']==m['id'] and f['displayName']==m['author']['displayName']=='Li Xiang'
assert f['numerator']==m['score']['numerator'] and f['denominator']==m['score']['denominator']
assert f['model']=='' and m['model'] is None
for key in ('summary','harness','method'): assert f[key]==m[key]
n,d=map(int,u['currentFormalRecord'].split('/'))
assert int(m['score']['numerator'])*d>n*int(m['score']['denominator'])
bench=json.loads((here/'pre-submit-benchmark.json').read_bytes())
assert bench['candidate_strictly_above_all_exact'] is True and bench['exact_rational_records_compared']==36
now=datetime.now(timezone.utc)
for stamp in (boundary['observed_UTC'],boundary['active']['observed_UTC']):
 assert 0<=(now-datetime.fromisoformat(stamp.replace('Z','+00:00'))).total_seconds()<=300
stamp=datetime.strptime(bench['observed_UTC'],'%Y-%m-%d %H:%M:%S UTC').replace(tzinfo=timezone.utc)
assert 0<=(now-stamp).total_seconds()<=300
pubpath=root/'research-goal-20261020-w9a2-v8-public-source-sync-v1/observation.json'
pub=json.loads(pubpath.read_bytes())
assert pub['HTTP_status']==200 and pub['exact_public_bytes_equal'] is True and pub['source_SHA256']==sha(source)
s=json.loads((root/'research-goal-20261016/direction-state.json').read_bytes())
assert s['last_review_number']==12 and s['main_rounds_since_review']==0 and s['v8_RSS_resource_route']['passed'] is False
gate={'schema':'root-fixed-v8-one-official-attempt-gate-v1','allow_one_submit':True,'max_submit_clicks':1,
 'source':pin(packet/'proof/Solution.lean'),'server_JSON':pin(packet/'submission.draft.json'),
 'expected_proofDigest':wire,'id':m['id'],'author':'Li Xiang','root_evidence':bound,
 'browser_boundary':pin(here/'browser-pre-submit-boundary.json'),'fresh_record':pin(here/'pre-submit-benchmark.json'),
 'fixed_public_source_observation':pin(pubpath),'material_checkpoint_commit_prefix':'61fa107',
 'authorization':'Prior direct human instruction to stop repeating local checks and submit an attempt as Li Xiang; same archive/Apache-2 terms confirmed by 同意并提交. Macro012 selects this fixed changed source with known local failures.',
 'local_resource_PASS':False,'fullchain_PASS':False,'official_ACCEPTED':False,
 'actual_submit_performed_when_gate_frozen':False,'after_click':'Observe actual digest and same job; no duplicate Submit on timeout or uncertainty.',
 'frozen_at_UTC':now.isoformat()}
out=here/'submit-once-gate.json'
assert not out.exists()
out.write_bytes((json.dumps(gate,ensure_ascii=False,indent=2)+'\n').encode())
rows=[pin(p)|{'path':p.name} for p in sorted(here.iterdir()) if p.is_file() and p.name!='files.json']
(here/'files.json').write_bytes((json.dumps({'schema':'fixed-v8-official-attempt-gate-files-v1','files':rows},indent=2)+'\n').encode())
print(json.dumps({'gate_sha256':sha(out.read_bytes()),'allow_one_submit':True,'expected_proofDigest':wire,'local_resource_PASS':False}))
