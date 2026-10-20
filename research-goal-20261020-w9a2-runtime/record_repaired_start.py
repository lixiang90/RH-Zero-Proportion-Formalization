"""Update live direction metadata, keeping historical acceptance scoped to its goal."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]
state_path=ROOT/'research-goal-20261016/direction-state.json'
state=json.loads(state_path.read_text(encoding='utf-8'))
assert state['main_rounds_since_review']==1 and state['last_review_number']==7
review=ROOT/state['last_review']
review_sha=hashlib.sha256(review.read_bytes()).hexdigest()
state.update(actual_goal_objective_achieved=False,
    prior_accepted_goal_remains_complete=True,
    current_analysis_task_status='Active W9A2 improvement goal; prior analysis and prior accepted submission remain historical evidence.',
    main_route='Fixed W9A2 quantitative leaf localization, 49-state weighted transition potential, actual counting and complete submission verification. Larger-gain curvature route parked in this proof-implementation round.',
    current_main_round_started_UTC=state['round_started_UTC'],
    last_review_SHA256=review_sha,last_review_sha256=review_sha,
    planned_early_review_reason='Review from round4 if progress becomes bookkeeping or evidence redirects; default6, never later8. A major counterexample or promising new certificate can trigger an immediate review.',
    next_gate='Complete explicitly repaired ordinary Core/Graph/Localization/Counting/Final; then exact regenerated single-file, Comparator/default Lean/nanoda within3200s, fresh strict record, GitHub synchronization and official submission materials.',
    remaining_required_work=[
        'Actual unconditional dyadic and cumulative improved proportion, complete repaired Lean proof and transitive standard-axiom audit',
        'Exact final source below2,000,000 bytes, fresh generated public statements and strict current record comparison',
        'Comparator statement/dependency/primitive comparison, default Lean and independent serial nanoda replay under one3200-second timer or verified official acceptance',
        'Synchronize final proof and evidence to GitHub with exact source consistency',
        'Deliver complete submission materials and verify official website acceptance; authentication currently absent in the available browser'])
current=state['w9a2_current_round']
current.update(ordinary_gate='research-goal-20261016/gates/w9a2-ordinary-v1b-20261020.json',
    ordinary_gate_SHA256='92def59e80c77b461e3cc301bff748f65e44d53b4c031d745098b156882a3bc5',
    ordinary_session=93720,ordinary_session_terminal_exit_code=None,
    currently_running_module='Core',current_Lean_PID=40944,
    previous_ordinary_failure_preserved='research-goal-20261020-w9a2-ordinary-v0-terminal',
    repair_manifest='research-goal-20261020-w9a2-core-repair-v1/files.json',
    repair_manifest_SHA256='9aafa909450a60295a0864982d8f3f596217fba54c8e04eeeb3a21eede8f5114',
    flat_draft_bytes=1829955,
    flat_draft_SHA256='8928832f3503d39ad6786ae26a394299779d3a53b7c590e7ca7df793ae7614f3',
    previous_v1_entry_aborted_before_candidate_and_job_creation=True,
    process_exclusion='Exact pinned4.33 executable; two unrelated4.32 user tasks remain untouched',
    updated_at_UTC=datetime.now(timezone.utc).isoformat())
state_path.write_bytes((json.dumps(state,ensure_ascii=False,indent=2)+'\n').encode())
p=ROOT/'research-goal-20261016/DIRECTION.zh.md'
raw=p.read_bytes()
heading='# 研究方向与宏观回顾\n'.encode()
assert raw.startswith(heading)
status=('\n当前有效入口：宏观007（macro-reviews/007-20261019.zh.md），本实际研究轮counter=1。'
        '当前W9A2继续改进goal保持active；下文旧accepted目标的完成状态仅属历史目标。'
        '本轮主线固定49状态加权证书的完整形式化与验收，不启动新的优化族。\n')
p.write_bytes(heading+status.encode()+raw[len(heading):])
p=ROOT/'research-goal-20261020-w9a2-runtime/CONTINUATION.zh.md'
paragraph=('\n\n最新唯一候选：ordinary-v1b gate92def59e…，session93720/Core40944。'
           'v1入口因全局Lean计数包含无关4.32.2用户任务而在候选和job创建前拒绝；'
           '另版runner633039e6…只排除同一固定4.33工具链，其他编译与数学步骤不变。'
           'Core修复仅加Bool.false_eq_true，完整manifest9aafa909…；旧v0保全。'
           'flatv1为1829955B/SHA8928832f…，未经完整验收。官网页仍同R但浏览器未登录。'
           'direction-state旧actual_goal=true与remaining=[]现已明确只保留于旧accepted证据；'
           '当前goal=false/remaining完整列出，review007哈希字段纠正一致，不增轮或重置。\n')
p.write_bytes(p.read_bytes()+paragraph.encode())
print(json.dumps({'counter':state['main_rounds_since_review'],'review':7,
                  'review_sha256':review_sha,'active_session':93720,'actual_goal_objective_achieved':False}))
