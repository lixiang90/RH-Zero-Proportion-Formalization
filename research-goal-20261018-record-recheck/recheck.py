"""Fresh read-only record metadata check. Never fetch large Lean source or replay it."""
from pathlib import Path
from fractions import Fraction
from urllib.parse import urlsplit
import base64,datetime,hashlib,json,time,urllib.request
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
STAMP=str(time.time_ns())
reads=[]
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def get(url):
 req=urllib.request.Request(url,headers={'User-Agent':'RH-Zero-independent-record-recheck/1','Cache-Control':'no-cache'})
 with urllib.request.urlopen(req,timeout=30) as r:
  raw=r.read(1_000_001);assert len(raw)<=1_000_000
  rec={'url':url,'final_url':r.geturl(),'HTTP_status':r.status,'read_UTC':utc(),
       'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),
       'headers':{k:r.headers.get(k) for k in ['Date','Age','X-Vercel-Cache','Cache-Control','ETag','Last-Modified','X-GitHub-Request-Id']}}
  assert r.status==200
 reads.append(rec);return json.loads(raw)
def score(r):
 x=r['exactRational'];return Fraction(int(x['numerator']),int(x['denominator']))
site=get('https://www.riemannzeta.fun/api/leaderboard?record_recheck='+STAMP)
ref=get('https://api.github.com/repos/josusanmartin/riemann/git/ref/heads/main?record_recheck='+STAMP)
head=ref['object']['sha']
commit=get('https://api.github.com/repos/josusanmartin/riemann/commits/'+head+'?record_recheck='+STAMP)
records=get('https://raw.githubusercontent.com/josusanmartin/riemann/'+head+'/data/records.json?record_recheck='+STAMP)
eligible=[r for r in records if r['track']=='critical-line' and r['status']=='kernel-verified']
highest=eligible[-1]  # matches upstream getCurrentRecord(): last kernel-verified entry
assert score(highest)==max(score(r) for r in eligible if r.get('exactRational'))
current=site['current']
proof=urlsplit(highest['proofUrl']).path.split('/blob/',1)[1]
proof_ref,proof_path=proof.split('/',1)
parent,name=proof_path.rsplit('/',1)
listing=get('https://api.github.com/repos/josusanmartin/riemann/contents/'+parent+'?ref='+proof_ref+'&record_recheck='+STAMP)
entry=next(r for r in listing if r['name']==name)
local=ROOT/'research-goal-20261018-record-source-audit/snapshot/Solution.lean'
raw=local.read_bytes();blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
baseline=Fraction(3337839448633819172184136761695440236797,4955319193847235264050000000000000000000)
obj={'scope':'Fresh site/repository metadata and source-byte identity only; no Lean, LP, leaf or kernel query.',
 'started_marker':STAMP,'finished_UTC':utc(),'reads':reads,
 'GitHub_main':head,'head_commit_UTC':commit['commit']['committer']['date'],
 'head_message':commit['commit']['message'],'site_current':current,'repository_current':highest,
 'repository_current_selection':'last kernel-verified entry, matching upstream getCurrentRecord',
 'repository_kernel_verified_count':len(eligible),'site_equals_repository_current':score(current)==score(highest),
 'legacy_entries_missing_exactRational':sum(not r.get('exactRational') for r in eligible),
 'current_is_highest_among_explicit_exact_rational_records':True,
 'local_baseline_exact':str(baseline),'current_equals_local_baseline':score(highest)==baseline,
 'higher_public_accepted_record_observed':score(highest)>baseline,
 'proof_ref':proof_ref,'proof_path':proof_path,'proof_metadata':{'bytes':entry['size'],'git_blob_sha1':entry['sha']},
 'local_snapshot':{'path':local.relative_to(ROOT).as_posix(),'bytes':len(raw),
   'sha256':hashlib.sha256(raw).hexdigest(),'git_blob_sha1':blob},
 'public_source_matches_local_snapshot':entry['sha']==blob and entry['size']==len(raw),
 'large_source_redownloaded':False,'website_kernel_verified_status_not_new_local_kernel_replay':True,
 'Lean_invocations':0,'LP_calls':0,'leaf_decoding_runs':0,'new_mathematical_bounds_computed':0,
 'technical_attempt':2,'previous_attempt':'TypeError on nullable legacy exactRational; no receipt produced, source was not downloaded',
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
p=HERE/'receipt.json'
with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(obj,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps({k:obj[k] for k in ['finished_UTC','GitHub_main','head_commit_UTC',
 'site_equals_repository_current','current_equals_local_baseline','higher_public_accepted_record_observed',
 'public_source_matches_local_snapshot']},ensure_ascii=False))
