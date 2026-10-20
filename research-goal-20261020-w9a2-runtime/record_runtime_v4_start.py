from pathlib import Path
from datetime import datetime, timezone
import json
ROOT=Path(__file__).resolve().parents[1]
job=ROOT/'tmp/w9a2-20261020/trusted-runtime-closure-v4'
start=json.loads((job/'started.json').read_text())
assert start['pid']==12340 and not (job/'terminal.json').exists()
p=ROOT/'research-goal-20261016/direction-state.json';state=json.loads(p.read_text(encoding='utf-8'))
assert state['main_rounds_since_review']==1 and state['last_review_number']==7
state['w9a2_current_round'].update(runtime_setup_session=89749,runtime_setup_pid=12340,
    runtime_setup_version=4,runtime_setup_terminal_exit_code=None,
    runtime_setup_scope='metadata-only source/cache closure; zero compiler/proof main runs',
    next_proof_gate='After actual v4 setup exit0 and all-pin review, one production cold single-file/Comparator/default Lean/serial nanoda check under3200s.')
p.write_bytes((json.dumps(state,ensure_ascii=False,indent=2)+'\n').encode())
paragraph='\n\n同一macro007+round1：root已审v4唯一Package.id?: Option String修复、独立类型依据和冻结清单，授权gate b1f228ffc5fb8bb60a9aa85740522266613895f8b1e46292cc1e18b2f5866fb8；实际metadata-only session89749/PID12340于08:07UTC开始。v4所有文件冻结至原句柄terminal及all-pin复核；proof_runs=0，未预认setup或完整证明验收PASS，counter=1。\n'
for rel in ['research-goal-20261016/DIRECTION.zh.md','research-goal-20261020-w9a2-runtime/CONTINUATION.zh.md']:
    p=ROOT/rel;p.write_bytes(p.read_bytes()+paragraph.encode())
print(json.dumps(dict(session=89749,pid=12340,proof_runs=0,counter=1)))
