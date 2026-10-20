"""Freeze actual repaired-Core PASS and first Graph diagnostic."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]
job=ROOT/'tmp/w9a2-20261020/candidate-ordinary-v1'
out=ROOT/'research-goal-20261020-w9a2-ordinary-v1-terminal'
out.mkdir(exist_ok=False)
names=['started.json','terminal.json']
for module in ['Core','Graph']:
    names += [f'StructuralW9A220261020_{module}.{suffix}' for suffix in
              ['command.json','child.json','log','receipt.json']]
rows=[]
for name in names:
    raw=(job/name).read_bytes()
    (out/name).write_bytes(raw)
    rows.append({'path':name,'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()})
core=json.loads((job/'StructuralW9A220261020_Core.receipt.json').read_text())
graph=json.loads((job/'StructuralW9A220261020_Graph.receipt.json').read_text())
assert core['ordinary_compile_passed'] and core['exit_code']==0
assert graph['exit_code']==1 and not json.loads((job/'terminal.json').read_text())['passed']
note={'observed_at_UTC':datetime.now(timezone.utc).isoformat(),
      'root_observed_parent_session':93720,'actual_parent_exit_code':1,
      'Core_ordinary_passed':True,'Graph_ordinary_passed':False,
      'failure_scope':'reverse_span normalization of reflected Fin constructors versus numeral notation, sole logged error148:70',
      'automatic_retry':False,'counter_changed':False,'files':rows,
      'Comparator_passed':False,'independent_kernel_passed':False,'website_submission_ready':False}
(out/'files.json').write_bytes((json.dumps(note,indent=2)+'\n').encode())
state_path=ROOT/'research-goal-20261016/direction-state.json'
state=json.loads(state_path.read_text(encoding='utf-8'))
current=state['w9a2_current_round']
current.update(ordinary_session_terminal_exit_code=1,current_Lean_PID=None,currently_running_module=None,
    Core_ordinary_passed_seconds=core['elapsed_seconds'],Core_olean_SHA256=core['olean_sha256'],
    Graph_ordinary_failed_seconds=graph['elapsed_seconds'],
    ordinary_failure_preserved=out.relative_to(ROOT).as_posix(),
    next_proof_gate='Minimal same-theorem Graph reverse_span Fin-index normalization repair; reuse exact passing Prefix/Core and compile Graph/Localization/Counting/Final')
state_path.write_bytes((json.dumps(state,ensure_ascii=False,indent=2)+'\n').encode())
paragraph=('\n\n同一macro007+round1：修复Core实际PASS588.859s/olean4e24ca21…；'
           '同一session93720在Graph64.250s真实terminal exit1。唯一error为reverse_span的Fin构造器/数字记号未统一，'
           '未报告有限图核算false。全部v1命令/日志/收据/终端保全ordinary-v1-terminal。'
           '只准备同命题Graph证明归一化修复，后续开发复用已PASS同SHA Prefix/Core；未自动重试、未改数学数据。'
           'counter仍1，最终全域比例/完整验收仍未完成。\n')
for rel in ['research-goal-20261016/DIRECTION.zh.md','research-goal-20261020-w9a2-runtime/CONTINUATION.zh.md']:
    p=ROOT/rel;p.write_bytes(p.read_bytes()+paragraph.encode())
print(json.dumps({'manifest_sha256':hashlib.sha256((out/'files.json').read_bytes()).hexdigest(),
                  'Core_passed_seconds':core['elapsed_seconds'],'Graph_exit':graph['exit_code']}))
