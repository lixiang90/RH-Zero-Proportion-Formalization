"""Preserve the actual first candidate exit without upgrading its scope."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
job = ROOT / 'tmp/w9a2-20261020/candidate-ordinary-v0'
out = ROOT / 'research-goal-20261020-w9a2-ordinary-v0-terminal'
out.mkdir(exist_ok=False)
names = ['started.json', 'terminal.json']
for module in ['Prefix', 'Core']:
    names += [f'StructuralW9A220261020_{module}.{suffix}' for suffix in
              ['command.json', 'child.json', 'log', 'receipt.json']]
rows = []
for name in names:
    raw = (job / name).read_bytes()
    (out / name).write_bytes(raw)
    rows.append({'path': name, 'bytes': len(raw),
                 'sha256': hashlib.sha256(raw).hexdigest()})
core = json.loads((out/'StructuralW9A220261020_Core.receipt.json').read_text())
terminal = json.loads((out/'terminal.json').read_text())
assert core['exit_code'] == 1 and not terminal['passed']
note = {'observed_at_utc': datetime.now(timezone.utc).isoformat(),
        'root_observed_parent_session': 68239, 'actual_parent_exit_code': 1,
        'Prefix_ordinary_passed': True, 'Core_ordinary_passed': False,
        'failure_scope': 'qTargetFrom_sound Bool false=true simplification; no failed finite check in log',
        'automatic_retry': False, 'Counter_or_review_changed': False,
        'Comparator_passed': False, 'independent_kernel_passed': False,
        'website_submission_ready': False, 'files': rows}
(out/'files.json').write_bytes((json.dumps(note, indent=2)+'\n').encode())
state_path = ROOT/'research-goal-20261016/direction-state.json'
state = json.loads(state_path.read_text(encoding='utf-8'))
current = state['w9a2_current_round']
current.update(ordinary_session_terminal_exit_code=1,
               currently_running_module=None, current_Lean_PID=None,
               Core_ordinary_failed_seconds=core['elapsed_seconds'],
               ordinary_failure_preserved=str(out.relative_to(ROOT)).replace('\\','/'),
               next_proof_gate='Versioned same-theorem Bool simplification repair, reuse unchanged passing Prefix, then Core and four remaining modules')
state_path.write_bytes((json.dumps(state,ensure_ascii=False,indent=2)+'\n').encode())
paragraph = ('\n\n同一macro007+round1：candidate68239真实terminal exit1；Prefix普通PASS436.328s，'
             'Core644.610s因qTargetFrom_sound中的if false=true未化简而失败，日志未报finite-check失败。'
             '原源码、命令、日志、receipt保存在research-goal-20261020-w9a2-ordinary-v0-terminal。'
             '只准备另版同命题proof-only修复并复用已PASS同SHA Prefix；没有自动重试、数学数据修改或新优化。'
             'Linux固定归档55718真实exit0，574905502B/SHA48010c7d…完整校验通过；尚未mirror或编译。'
             'counter仍1，最终无条件比例/单源/Comparator/独核/3200s/官网接受未完成。\n')
for rel in ['research-goal-20261016/DIRECTION.zh.md',
            'research-goal-20261020-w9a2-runtime/CONTINUATION.zh.md']:
    p=ROOT/rel
    p.write_bytes(p.read_bytes()+paragraph.encode())
print(json.dumps({'preserved':str(out.relative_to(ROOT)), 'files':len(rows),
                  'manifest_sha256':hashlib.sha256((out/'files.json').read_bytes()).hexdigest()}))
