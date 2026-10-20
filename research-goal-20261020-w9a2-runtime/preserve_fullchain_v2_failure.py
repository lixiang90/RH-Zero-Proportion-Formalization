"""Preserve the actual timed-out parent without upgrading partial checks."""
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib
ROOT=Path(__file__).resolve().parents[1];job=ROOT/'tmp/w9a2-20261020/fullchain-v2';out=ROOT/'research-goal-20261020-w9a2-fullchain-v2-terminal'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_bytes())
def write(p,v):
    with p.open('xb') as f:f.write((json.dumps(v,ensure_ascii=False,indent=2)+'\n').encode())
raw=load(out/'original-parent-exit.json');failure=load(job/'failure.json');start=load(job/'started.json')
assert raw['session']==68962 and raw['parent_pid']==start['pid']==49320 and raw['actual_original_handle_result']['exit_code']==1
assert failure['error_type']=='TimeoutExpired' and failure['stage']=='comparator-default-Lean-kernel'
assert 3200<=failure['elapsed_at_failure_seconds']<3220 and failure['ordinary_single_file_passed']
assert failure['source_sha256']=='a517df6aebde6d136f8b83e06c8be10b3413b8430390f52bd47f04e06f0dce26'
assert not (job/'terminal.json').exists() and not (job/'verification.json').exists() and not (job/'nanoda-config.json').exists()
for p in sorted(job.rglob('*')):
    if not p.is_file() or p.suffix not in ['.json','.log','.lean']:continue
    dest=out/'job'/p.relative_to(job);dest.parent.mkdir(parents=True,exist_ok=True)
    with dest.open('xb') as f:f.write(p.read_bytes())
    assert sha(dest)==sha(p)
artifacts=[]
for p in sorted([*job.glob('*.ndjson'),*job.glob('lib/**/*.olean')]):
    artifacts.append(dict(path=p.relative_to(ROOT).as_posix(),bytes=p.stat().st_size,sha256=sha(p),retained_at_original_path=True,duplicated_into_git=False))
write(out/'retained-binary-and-export-artifacts.json',artifacts)
write(out/'root-parent-exit-attestation.json',dict(schema='w9a2-root-timed-out-fullchain-v2',sole_owner='/root',exec_session_id=68962,parent_pid=49320,actual_exit_code=1,observed_scope='completed-outer-parent-handle',observation_source='functions.write_stdin',raw_result='original-parent-exit.json',observed_at_utc=datetime.now(timezone.utc).isoformat(),ordinary_single_file_passed=True,source_bytes=1830052,source_sha256=failure['source_sha256'],two_native_exports_passed=True,Comparator_passed=False,default_kernel_replay_passed=False,nanoda_started=False,fullchain_passed=False,official_website_acceptance=False,submitted=False,elapsed_at_failure_seconds=failure['elapsed_at_failure_seconds'],failure_kind='Total3200s deadline interrupted CoreAudit; not a returned mathematical rejection. No audit completion is claimed.'))
rows=[dict(path=p.relative_to(out).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(out.rglob('*')) if p.is_file()]
write(out/'files.json',dict(scope='Actual fullchain-v2 deadline failure, source compilation and exports only PASS; neither independent kernel nor complete3200s PASS',files=rows))
p=ROOT/'research-goal-20261016/direction-state.json';state=load(p)
assert state['main_rounds_since_review']==1 and state['last_review_number']==7
state['w9a2_current_round'].update(production_terminal_exit_code=1,production_failure_evidence=out.relative_to(ROOT).as_posix(),production_fullchain_passed=False,next_proof_gate='Written macro008 review, then separately gated replay of exact existing exports; official fixed3200 acceptance remains required.')
state['current_formal_candidate'].update(single_file_ordinary_Lean_proven=True,production_3200_passed=False,independent_kernels_passed=False,website_ready=False)
state['current_analysis_task_status']='Exact frozen single-file ordinary Lean PASS and exports PASS. Local cold3200 run timed out during CoreAudit; no Comparator/default replay/Nano PASS or website submission.'
p.write_bytes((json.dumps(state,ensure_ascii=False,indent=2)+'\n').encode())
note='\n\n同一macro007+round1：fullchain-v2原session68962/PID49320实际exit1，3200.578秒，TimeoutExpired中止CoreAudit（仅余683.390秒）；没有Comparator/default replay完成收据，也没有Nano。a517/1830052B单文件普通Lean实际PASS1150.328秒，全部15roots仅标准三公理；两native exports实际PASS266.594/53.953秒，原源/导出对象/olean均保留，完整小收据与SHA封fullchain-v2-terminal。未提交官网、未称数学拒绝或全链通过。17万runtime文件重复来源复核构成显著额外成本；下一步须书面宏观008审定复用已验导出补独立重放，并以官网固定3200接受作为最终整轮验收。此处尚未重置counter=1/review7，未自动重试。\n'
for rel in ['research-goal-20261016/DIRECTION.zh.md','research-goal-20261020-w9a2-runtime/CONTINUATION.zh.md']:
    p=ROOT/rel;p.write_bytes(p.read_bytes()+note.encode())
print(json.dumps(dict(manifest_sha256=sha(out/'files.json'),retained_artifacts=artifacts,actual_exit_code=1,fullchain_passed=False)))
