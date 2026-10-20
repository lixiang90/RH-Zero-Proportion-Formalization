"""Actual ordinary mathematics is complete; all production/official gates remain."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]
p=ROOT/'research-goal-20261016/direction-state.json'
s=json.loads(p.read_text(encoding='utf-8'));assert s['main_rounds_since_review']==1
final=json.loads((ROOT/'tmp/w9a2-20261020/candidate-ordinary-v5/StructuralW9A220261020_Final.receipt.json').read_text())
terminal=json.loads((ROOT/'tmp/w9a2-20261020/candidate-ordinary-v5/terminal.json').read_text())
assert terminal['passed'] and final['ordinary_compile_passed'] and final['axiom_audit_passed']
assert len(final['observed_axioms'])==7 and all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in final['observed_axioms'].values())
s['actual_goal_objective_achieved']=False
s['current_analysis_task_status']='Actual unconditional W9A2 dyadic/cumulative theorem and strict exact improvement proved in ordinary Lean; production single-file/dual-kernel/timer/GitHub/official acceptance still pending.'
s['remaining_required_work']=s['remaining_required_work'][1:]
c=s['current_unformalized_candidate']
c['actual_full_Lean_proven']=True;c['website_ready']=False
s['current_formal_candidate']={**c,'ordinary_final_receipt':'research-goal-20261020-w9a2-ordinary-v5-terminal/StructuralW9A220261020_Final.receipt.json',
    'actual_ordinary_parent_session':1250,'actual_parent_exit_code':0,
    'seven_transitive_roots_allowed_axioms_only':True,'single_file_and_production_not_yet_verified':True}
s['w9a2_current_round'].update(currently_running_module=None,current_Lean_PID=None,
    ordinary_gate='research-goal-20261016/gates/w9a2-ordinary-v5-20261020.json',
    ordinary_gate_SHA256='5a928e8066bd0c8a1bb3cd9e28028b9c995dd40728eed3e72612f9ca8f086d0e',
    ordinary_session=1250,ordinary_session_terminal_exit_code=0,
    ordinary_terminal_preserved='research-goal-20261020-w9a2-ordinary-v5-terminal',
    full_prepared_modules_bytes=1827832,actual_unconditional_mathematics_ordinary_proved=True,
    flat_draft_bytes=1830001,flat_draft_SHA256='650ad1762ee36ba1ddf5f6a027900b20f0f85ba087ac099fd2c99a54eaf6ae13',
    runtime_setup_current_session=44009,runtime_setup_status='Source-import closure passed, official SDK archive member comparison active; no compiler/proof in setup',
    updated_at_UTC=datetime.now(timezone.utc).isoformat())
s['w9a2_current_round'].pop('ordinary_failure_preserved',None)
p.write_bytes((json.dumps(s,ensure_ascii=False,indent=2)+'\n').encode())
paragraph=('\n\n同一macro007+round1数学关实际完成：Final单模块原session1250真实exit0/12.657s，'
           '七个传递审计root均仅标准三公理，无sorryAx。此前Counting五个root同样通过。'
           '故固定49状态加权certificate的actual ζ无条件dyadic/cumulative严格新比例已在普通Lean成立；'
           '这是开发复用精确PASS依赖的结果，尚非单源cold或全链预算通过。'
           '新flatv5为1830001B/SHA650ad176…；准确单源/Comparator/defaultkernel/Nano/统一3200s/最新R/GitHub/官网接受仍待。'
           'runtime setup44009正查官方SDK archive13938成员，0compiler/proof，活目录v2禁止修改。'
           '用户已明确授权验证后提交Li Xiang；浏览器实见@lixiang90登录且3/3上传额度。counter保持1。\n')
for rel in ['research-goal-20261016/DIRECTION.zh.md','research-goal-20261020-w9a2-runtime/CONTINUATION.zh.md']:
    p=ROOT/rel;p.write_bytes(p.read_bytes()+paragraph.encode())
print(json.dumps({'actual_unconditional_ordinary_proved':True,'actual_goal_objective_achieved':False,'remaining':len(s['remaining_required_work']),'counter':1}))
