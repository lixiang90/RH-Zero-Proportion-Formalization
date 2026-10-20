"""Archive a root-observed failed metadata process, never a proof PASS."""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import gzip
import hashlib
import json
ROOT=Path(__file__).resolve().parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--version',type=int,required=True)
ap.add_argument('--session',type=int,required=True);ap.add_argument('--failure',required=True)
args=ap.parse_args();assert args.version==4 and args.session==89749
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text(encoding='utf-8'))
job=ROOT/f'tmp/w9a2-20261020/trusted-runtime-closure-v{args.version}'
out=ROOT/f'research-goal-20261020-w9a2-runtime-v{args.version}-terminal'
terminal=load(job/'terminal.json');assert terminal['exit_code']==1 and terminal['proof_runs']==0
out.mkdir(exist_ok=False)
for name in ['started.json','terminal.json']:(out/name).write_bytes((job/name).read_bytes())
raw=(job/'official-sdk-check.json').read_bytes()
(out/'official-sdk-check.json.gz').write_bytes(gzip.compress(raw,mtime=0))
attestation=dict(schema='w9a2-root-failed-setup-terminal-v1',sole_owner='/root',
    original_exec_session_id=args.session,actual_parent_exit_code=1,parent_pid=terminal['assembler_pid'],
    source='Root observed original functions.write_stdin terminal exit1, not inferred from PID disappearance',
    observed_at_utc=datetime.now(timezone.utc).isoformat(),failure=args.failure,
    metadata_only=True,proof_runs=0,complete_runtime_setup_passed=False,
    SDK_component_raw_sha256=hashlib.sha256(raw).hexdigest())
(out/'root-parent-exit-attestation.json').write_bytes((json.dumps(attestation,indent=2)+'\n').encode())
rows=[dict(path=p.name,bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(out.iterdir())]
(out/'files.json').write_bytes((json.dumps(dict(scope='Actual failed metadata-only setup',files=rows),indent=2)+'\n').encode())
p=ROOT/'research-goal-20261016/direction-state.json';state=load(p)
assert state['main_rounds_since_review']==1 and state['last_review_number']==7
current=state['w9a2_current_round'];current['runtime_setup_terminal_exit_code']=1
current['runtime_closure_v4_terminal']=dict(session=args.session,exit_code=1,
    evidence=out.relative_to(ROOT).as_posix(),failure=args.failure,proof_runs=0)
p.write_bytes((json.dumps(state,ensure_ascii=False,indent=2)+'\n').encode())
paragraph='\n\n同一macro007+round1：runtime-v4 original89749/PID12340实际exit1，String字段修复通过后，检查器把至少一个现代Zeta模块误送入legacy-only trace路径。全部输入/失败收据冻结；proof_runs=0。下一步先全量静审所有Zeta现代/legacy trace与剩余tail前提，确认完整修复再授权新metadata版本；数学源码、证明与counter=1不变。\n'
for rel in ['research-goal-20261016/DIRECTION.zh.md','research-goal-20261020-w9a2-runtime/CONTINUATION.zh.md']:
    p=ROOT/rel;p.write_bytes(p.read_bytes()+paragraph.encode())
print(json.dumps(dict(preserved=out.relative_to(ROOT).as_posix(),manifest_sha256=sha(out/'files.json'),actual_exit=1)))
