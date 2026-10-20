"""Metadata-only record of macro012. No proof or website action."""
from pathlib import Path
import hashlib, json
root=Path(__file__).resolve().parents[1]
here=Path(__file__).resolve().parent
review='research-goal-20261016/macro-reviews/012-20261020.zh.md'
review_sha='fb7516e57e8fe56802d16b088178c29215d10161a10060a1e007e2b7a9274347'
def sha(raw): return hashlib.sha256(raw).hexdigest()
def encoded(x): return (json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode()
assert sha((root/review).read_bytes())==review_sha
evidence=[
 ('research-goal-20261020-w9a2-v8-resource-failure-v2/files.json','31913deddce2ab5ebd5d4efd27d80102c64a54423334095489f13f7589ab2942'),
 ('research-goal-20261020-w9a2-v8-interpreter-static-formal/files.json','cba2e917e9ff83b9d3602e0639e9cc40641bff34ea3bf8328c208913a23137d3'),
 ('research-goal-20261020-w9a2-v8-infotree-static-independent/files.json','025c1ab94c6c01ff41556fb5970e3c34089e434706297e4c3d3c185a702173fd')]
checked=[]
for name, expected in evidence:
 p=root/name
 assert sha(p.read_bytes())==expected,name
 rows=json.loads(p.read_bytes())['files']
 for row in rows:
  q=root/row['path'] if row['path'].startswith(p.parent.relative_to(root).as_posix()+'/') else p.parent/row['path']
  b=q.read_bytes()
  assert len(b)==row['bytes'] and sha(b)==row['sha256'],str(q)
 checked.append({'path':name,'sha256':expected,'files_checked':len(rows)})
benchmark=json.loads((here/'benchmark-observation.json').read_bytes())
assert benchmark['strictly_greater_than_all_exact_compared'] and benchmark['exact_rational_records_compared']==36
p=root/'research-goal-20261016/direction-state.json'
s=json.loads(p.read_bytes())
assert s['last_review_number']==11 and s['main_rounds_since_review']==1
s.update({'last_review_number':12,'main_rounds_since_review':0,'last_review':review,'last_review_path':review,
 'last_review_SHA256':review_sha,'last_review_sha256':review_sha,
 'counter_reset_reason':'Written macro012 completed in the first post93095-failure diagnostic round. Finite interpreter/InfoTree evidence closed; fixed v8 goes to official attempt under existing human authorization. No new tool/agent/compaction round.',
 'main_route':'Preserve all local failures. Under the human instruction to stop repeating checks and submit an attempt, prepare honest fixed-v8 attempt materials and use the original official8GB/3200s full-kernel pipeline once. No more local full proof replay or raised local limits.',
 'next_gate':'Independently review attempt-v8 materials, fresh UI login/quota/no-active-job and currentR<K, exact public source sync; freeze delivery gate, upload fixed v8 as Li Xiang once, then observe the same actual official job. Official acceptance is unknown.',
 'optimization_scope':'All mathematics and source frozen. No InfoTree false directive/hook/wrapper, new compiler batch, new data/checker/numerical family or parameter increase.',
 'website_submission_ready':False,
 'v8_official_attempt_route':{'review':12,'review_sha256':review_sha,'evidence':checked,'source_sha256':'5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b','source_bytes':1829382,'local_resource_pass':False,'old_ready_generator_permitted':False,'full_local_replay_permitted':False,'status':'attempt_materials_pending','submitted':False,'official_acceptance':False,'goal_complete':False}})
p.write_bytes(encoded(s))
prefix=('当前权威宏观012（'+review+'，SHA'+review_sha+'）已书面完成，counter1→0/review12。原93095解释器memory_exception真实失败不变，旧ready生成器条件false禁止执行。InfoTree裸关闭会空tree panic，停止该方向。按人类已明确不重复核查、直接提交尝试的授权，下一关只诚实attempt-v8材料/鲜核R与quota/无活任务/Git逐字一致，随后官网原8GB/3200秒完整双核只尝试固定v8一次，Li Xiang；不再本地full重跑或提高-M6500。此选择替代旧resourcePASS交付前提但绝不把失败翻PASS。14:57:09Z新R仍旧分数，K严格更高；官方成功未知。完整无条件数学/双核/公开推广/Git目标保持active。\n\n')
for name in ('research-goal-20261016/DIRECTION.zh.md','research-goal-20261020-w9a2-runtime/CONTINUATION.zh.md'):
 q=root/name
 q.write_bytes(prefix.encode()+q.read_bytes())
out=here/'review-record.json'
assert not out.exists()
out.write_bytes(encoded({'review':12,'review_sha256':review_sha,'evidence':checked,'counter_transition':[1,0],'new_compiler_runs':0,'official_submitted':False,'local_failures_stay_failed':True}))
print(json.dumps({'review':12,'counter':0,'evidence_files_valid':True,'new_compiler_runs':0}))
