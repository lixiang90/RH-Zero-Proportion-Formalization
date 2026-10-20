from pathlib import Path
import json

root = Path(__file__).resolve().parents[1]
p = root / 'research-goal-20261016/direction-state.json'
state = json.loads(p.read_text(encoding='utf-8'))
assert state['last_review_number'] == 9 and state['main_rounds_since_review'] == 0
state['main_rounds_since_review'] = 1
state['previous_goal_turn_classification'] = 'verified_wait'
state['main_route'] = 'Official v7 terminated: Building Solution.Candidate (1014s), Lean exit137, outer build/bash1. The UI lean-elaboration-failed and line2057 refer to a warning, not an observed source type error. Diagnose proof-production resource pressure while preserving the complete mathematical candidate.'
state['next_gate'] = 'One static resource diagnosis using actual v7 logs, pinned SDK and fixed official runtime source. No unchanged submission or local compiler/export/kernel/solver run. Distinguish proven SIGKILL-style exit from unconfirmed OOM cause; select one concrete proof-preserving resource change for written review before execution.'
state['optimization_scope'] = 'W9A2 mathematics, numeric packets and 49-state graph remain frozen. V7 has a real terminal resource-related failure, not a mathematical verdict. Static diagnosis only; no automatic further upload or compiler family.'
state['v7_delivery_route'].update({'official_result':'failed','official_diagnosis_code':'lean-elaboration-failed','actual_build_stage_seconds':1014,'actual_Lean_exit_code':137,'actual_outer_bash_exit_code':1,'OOM_confirmed':False,'official_acceptance':False,'official_kernels_complete':False})
state['resource_diagnostic_round'] = {'started_UTC':'2026-10-20T13:29:31Z','review':9,'counter_transition':[0,1],'new_numerical_family':False,'local_proof_execution':False}
p.write_bytes((json.dumps(state, ensure_ascii=False, indent=2) + '\n').encode('utf-8'))
prefix = ('13:29:31Z新终态覆盖下方running：官网v7实际Building Solution.Candidate(1014s)失败，Lean exit137、build/bash1；页面lean-elaboration-failed/Solution:2057只是提取到第一条push_neg弃用warning，并无该处type错误证据。进程被强制终止，OOM是待核假设而非已证明原因。用户已贴完整原日志，root另保存实际DOM日志。现启动宏观009后第1实际资源诊断轮，counter0→1；只静态审固定官方runtime/SDK与源资源成本，保留v7/首投/数值包全部冻结。不原样重投、不重复local Lean/export/kernel、不新增数值优化。完整无条件目标、双内核/官方接受/2MB/整轮限时/Git同步仍待，goal active。\n\n')
for name in ['research-goal-20261016/DIRECTION.zh.md','research-goal-20261020-w9a2-runtime/CONTINUATION.zh.md']:
    path = root / name
    path.write_bytes(prefix.encode('utf-8') + path.read_bytes())
print('Started actual post-v7-failure resource diagnostic round: review9/counter1; no proof execution.')
