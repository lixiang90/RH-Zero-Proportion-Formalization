"""Preserve the actual failed metadata-only v3 process, without proof claims."""
from pathlib import Path
from datetime import datetime, timezone
import gzip
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
out = ROOT / 'research-goal-20261020-w9a2-runtime-v3-terminal'
job = ROOT / 'tmp/w9a2-20261020/trusted-runtime-closure-v3'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda p: json.loads(p.read_text(encoding='utf-8'))
assert load(out / 'raw-root-tool-result.json')['exit_code'] == 1
assert load(job / 'terminal.json')['exit_code'] == 1
assert load(job / 'terminal.json')['assembler_pid'] == 44480
assert load(job / 'terminal.json')['proof_runs'] == 0
rows = []
for name in ['started.json', 'terminal.json']:
    (out / name).write_bytes((job / name).read_bytes())
raw = (job / 'official-sdk-check.json').read_bytes()
(out / 'official-sdk-check.json.gz').write_bytes(gzip.compress(raw, mtime=0))
attestation = dict(schema='w9a2-root-terminal-observation-v1', sole_owner='/root',
    role='trusted-runtime-closure-v1', exec_session_id=66541, parent_pid=44480,
    actual_exit_code=1, observed_scope='completed-outer-parent-handle',
    observation_source='functions.write_stdin', observed_at_utc=datetime.now(timezone.utc).isoformat(),
    raw_tool_terminal=dict(path=str(out/'raw-root-tool-result.json'), sha256=sha(out/'raw-root-tool-result.json')),
    proof_runs=0, complete_runtime_setup_passed=False,
    failure_scope='Metadata assertion used Name hashing for Package.id?: Option String; compiler and proof kernels did not run.',
    prior_official_sdk_component_raw_sha256=hashlib.sha256(raw).hexdigest())
(out/'root-parent-exit-attestation.json').write_bytes((json.dumps(attestation,indent=2)+'\n').encode())
for p in sorted(out.iterdir()):
    if p.is_file(): rows.append(dict(path=p.name,bytes=p.stat().st_size,sha256=sha(p)))
(out/'files.json').write_bytes((json.dumps(dict(scope='Actual failed metadata-only setup, no complete runtime/proof PASS',files=rows),indent=2)+'\n').encode())
p=ROOT/'research-goal-20261016/direction-state.json'
state=load(p); counter=state['main_rounds_since_review']
state['w9a2_current_round']['runtime_closure_v3_terminal']=dict(session=66541,exit_code=1,
    evidence=out.relative_to(ROOT).as_posix(),proof_runs=0,complete_runtime_passed=False)
assert counter==1 and state['last_review_number']==7
p.write_bytes((json.dumps(state,ensure_ascii=False,indent=2)+'\n').encode())
paragraph='\n\n同一macro007+round1：metadata-only runtime v3 原session66541实际exit1，PID44480，proof_runs=0；已核对10000个source-cache模块后，Zeta23 Package.id?: Option String被检查器误按Name散列，元数据断言失败。原v3与SDK组件收据、原句柄退出均冻结；完整runtime、生产单文件和双内核均未因此PASS。仅准备新版本最小类型修复，数学源码与counter=1保持不变。\n'
for rel in ['research-goal-20261016/DIRECTION.zh.md','research-goal-20261020-w9a2-runtime/CONTINUATION.zh.md']:
    p=ROOT/rel;p.write_bytes(p.read_bytes()+paragraph.encode())
print(json.dumps(dict(preserved=out.relative_to(ROOT).as_posix(),manifest_sha256=sha(out/'files.json'),actual_exit_code=1,proof_runs=0)))
