"""Archive the actual failed cold attempt; never infer a proof success."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json
ROOT=Path(__file__).resolve().parents[1]
job=ROOT/'tmp/w9a2-20261020/fullchain-v1'
out=ROOT/'research-goal-20261020-w9a2-fullchain-v1-terminal'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text(encoding='utf-8'))
def write(p,v):
    with p.open('xb') as f:f.write((json.dumps(v,ensure_ascii=False,indent=2)+'\n').encode())
raw=load(out/'original-parent-exit.json')
assert raw['session']==68653 and raw['parent_pid']==48644
assert raw['actual_original_handle_result']['exit_code']==1
fail=load(job/'failure.json');start=load(job/'started.json')
assert start['pid']==48644 and fail['failed'] and not fail['local_fullchain_verified']
assert fail['stage']=='ordinary-Solution.Candidate' and fail['stages'][-1]['exit_code']==1
assert fail['source_sha256']=='650ad1762ee36ba1ddf5f6a027900b20f0f85ba087ac099fd2c99a54eaf6ae13'
assert fail['elapsed_at_failure_seconds']<3200
assert sha(job/'logs/ordinary-Solution.Candidate.log')=='e02e5ca0b3fa36045f28831eb7553cdd61e829345af9100d330771880f4f2224'
assert not any((job/n).exists() for n in ['verification.json','deadline-receipt.json','terminal.json'])
transport=[]
for p in sorted(job.rglob('*')):
    if not p.is_file() or p.suffix not in ['.json','.log','.lean']:continue
    rel=p.relative_to(job);dest=out/'job'/rel;dest.parent.mkdir(parents=True,exist_ok=True)
    with dest.open('xb') as f:f.write(p.read_bytes())
    assert sha(dest)==sha(p)
    transport.append(dict(original=p.relative_to(ROOT).as_posix(),archive=dest.relative_to(out).as_posix(),bytes=p.stat().st_size,sha256=sha(p)))
write(out/'archive-map.json',transport)
write(out/'root-parent-exit-attestation.json',dict(schema='w9a2-root-failed-fullchain-v1',sole_owner='/root',exec_session_id=68653,parent_pid=48644,actual_exit_code=1,observed_scope='completed-outer-parent-handle',raw_result='original-parent-exit.json',observed_at_utc=datetime.now(timezone.utc).isoformat(),candidate_compile_exit_code=1,elapsed_seconds=fail['elapsed_at_failure_seconds'],timeout=False,Comparator_started=False,default_kernel_replay_started=False,nanoda_started=False,fullchain_passed=False,official_website_acceptance=False,submitted=False,diagnostic_scope='Three flattened wfun ambiguities and downstream linarith failure. sorryAx output from failed declarations is rejected, not a proof.'))
rows=[dict(path=p.relative_to(out).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(out.rglob('*')) if p.is_file()]
write(out/'files.json',dict(scope='Actual failed production parent exit1; no fullchain or official acceptance',files=rows))
p=ROOT/'research-goal-20261016/direction-state.json';state=load(p)
assert state['main_rounds_since_review']==1 and state['last_review_number']==7
state['w9a2_current_round'].update(production_terminal_exit_code=1,production_failure_evidence=out.relative_to(ROOT).as_posix(),production_fullchain_passed=False,next_proof_gate='Versioned qualification-only Counting repair, independent static review, one pinned Counting/Final development check, then a new frozen single-file cold fullchain attempt.')
state['current_analysis_task_status']='Original modular unconditional theorem proved; production v1 flattened compilation failed on namespace ambiguity. Preserve failure, qualify intended wfun, then verify a new frozen candidate; no Comparator/Nano/official acceptance yet.'
p.write_bytes((json.dumps(state,ensure_ascii=False,indent=2)+'\n').encode())
note='\n\n同一macro007+round1：fullchain-v1原session68653/PID48644已实际terminal exit1，整链1226.172秒、Candidate编译1091.172秒，非timeout。三处wfun因flat中AMW.Cert与Zeta23Ext.Bridge同时可见而歧义，随后linarith失败；失败声明的sorryAx诊断全部拒绝。未运行Comparator/default-kernel replay/nanoda，未提交官网。原始父退出、源、日志和全部收据封存fullchain-v1-terminal。下一关仅作versioned Counting限定名修复与独立审查，明确新gate后再验证，旧证书与旧attempt不改；counter=1、review=7不变。\n'
for rel in ['research-goal-20261016/DIRECTION.zh.md','research-goal-20261020-w9a2-runtime/CONTINUATION.zh.md']:
    p=ROOT/rel;p.write_bytes(p.read_bytes()+note.encode())
print(json.dumps(dict(archive=out.relative_to(ROOT).as_posix(),manifest_sha256=sha(out/'files.json'),files=len(rows),actual_exit_code=1,fullchain_passed=False)))
