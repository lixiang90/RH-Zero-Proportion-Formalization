"""Seal root-observed metadata completion; no compiler/kernel success claim."""
from pathlib import Path
from datetime import datetime, timezone
import gzip
import hashlib
import json
ROOT=Path(__file__).resolve().parents[1]
job=ROOT/'tmp/w9a2-20261020/trusted-runtime-closure-v5'
out=ROOT/'research-goal-20261020-w9a2-runtime-v5-terminal'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text(encoding='utf-8'))
def row(p):return dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p))
raw=load(out/'raw-root-tool-result.json')
assert raw['exit_code']==0 and isinstance(raw['output'],str)
assert raw.get('session_id') in [None,35077]
terminal=load(job/'terminal.json');start=load(job/'started.json')
assert terminal['exit_code']==0 and terminal['assembler_pid']==start['pid']==40712
assert terminal['proof_runs']==0
assert not (out/'files.json').exists()
prep=ROOT/'research-goal-20261020-w9a2-runtime-closure-v5/prepared-files.json'
assert sha(prep)=='6409c13165eee868c41af4030a77a902efa465198181c2a334bb2fe765a37930'
for r in load(prep)['files']:
    p=prep.parent/r['path'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
runner=prep.parent/'assemble.py';gate=ROOT/'research-goal-20261016/gates/w9a2-runtime-closure-v5-20261020.json'
assert sha(gate)=='f7b311f7e78697f776844e2ad462cc4ed33163dbbf2eb786dca92f59bb0380f1'
closure=load(job/'closure.json');receipt=load(job/'read-only-setup-receipt.json')
assert terminal['closure']['sha256']==sha(job/'closure.json')
assert receipt['assembler_pid']==40712 and receipt['assembler_sha256']==sha(runner)
assert receipt['proof_runs']==0 and receipt['user_proofs_compiled_or_reused_in_setup'] is False
assert closure['complete_source_bound_runtime_closure_verified']
assert closure['official_runtime_equivalence_claimed'] is False
assert closure['user_proofs_compiled_or_reused_in_setup'] is False
assert closure['trusted_setup_receipt']['sha256']==sha(job/'read-only-setup-receipt.json')
observation=dict(schema='w9a2-root-terminal-observation-v1',sole_owner='/root',
    role='trusted-runtime-closure-v1',exec_session_id=35077,parent_pid=40712,
    actual_exit_code=0,observed_scope='completed-outer-parent-handle',
    observation_source='functions.write_stdin',observed_at_utc=datetime.now(timezone.utc).isoformat(),
    raw_tool_terminal=row(out/'raw-root-tool-result.json'),runner=row(runner),gate=row(gate),
    completion_receipt=row(job/'read-only-setup-receipt.json'),proof_runs=0,
    production_fullchain_passed=False,official_website_acceptance=False)
(out/'root-parent-exit-attestation.json').write_bytes((json.dumps(observation,indent=2)+'\n').encode())
transports=[]
for p in sorted(job.iterdir()):
    if not p.is_file():continue
    data=p.read_bytes();name=p.name+('.gz' if len(data)>1000000 else '')
    target=out/name
    with target.open('xb') as f:f.write(gzip.compress(data,mtime=0) if len(data)>1000000 else data)
    transports.append(dict(original=row(p),transport_file=name,
        compressed=len(data)>1000000,lossless_raw_sha256=hashlib.sha256(data).hexdigest()))
(out/'transport.json').write_bytes((json.dumps(transports,indent=2)+'\n').encode())
files=[dict(path=p.name,bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(out.iterdir())]
(out/'files.json').write_bytes((json.dumps(dict(scope='Actual source-bound metadata-only runtime setup; no candidate compilation/dual kernel/fullchain PASS',files=files),indent=2)+'\n').encode())
p=ROOT/'research-goal-20261016/direction-state.json';state=load(p)
assert state['main_rounds_since_review']==1 and state['last_review_number']==7
state['w9a2_current_round'].update(runtime_setup_terminal_exit_code=0,
    runtime_setup_evidence=out.relative_to(ROOT).as_posix(),
    runtime_setup_source_bound_complete=True,production_fullchain_passed=False,
    next_proof_gate='One fresh cold single-file, Comparator/default Lean/serial nanoda chain under3200s, with current-record recheck and root actual outer exit.')
p.write_bytes((json.dumps(state,ensure_ascii=False,indent=2)+'\n').encode())
note='\n\n同一macro007+round1：metadata-only v5原session35077/PID40712已由root实际观察terminal exit0；全部11144模块source/cache来源、13951 SDK成员、干净overlay、五tool olean、native工具及WSL依赖完整核验成功。冻结v5准备清单当前SHA全同。原句柄raw结果、setup receipt/closure与无损运输已封runtime-v5-terminal；这不是candidate单文件、Comparator/双核或3200s验收。下一关为新鲜R与完整来源all-pin preflight后，唯一冷生产全链；counter=1不变。\n'
for rel in ['research-goal-20261016/DIRECTION.zh.md','research-goal-20261020-w9a2-runtime/CONTINUATION.zh.md']:
    p=ROOT/rel;p.write_bytes(p.read_bytes()+note.encode())
print(json.dumps(dict(manifest_sha256=sha(out/'files.json'),outer_observation=row(out/'root-parent-exit-attestation.json'),runtime_closure=row(job/'closure.json'),proof_runs=0)))
