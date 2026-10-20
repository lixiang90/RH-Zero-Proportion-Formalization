from pathlib import Path
import hashlib
import json

root=Path(__file__).resolve().parents[1]
work=root/'tmp/w9a2-20261020/v8-resource-v1'
raw=(work/'terminal.json').read_bytes()
assert hashlib.sha256(raw).hexdigest()=='b9e50233b9a50ecd9dd14945e2cce321d70d70ef05fec62fd6bcb4a1a001a162'
t=json.loads(raw)
assert t['resource_limit_exceeded'] is True and t['compiler_resource_gate_passed'] is False
assert t['actual_child_exit_code']==1 and t['parent_pid']==54132 and t['child_pid']==12924
observation={'schema':'actual-v8-resource-failure-root-observation-v1',
 'original_outer_session_id':72573,'actual_original_outer_exit_code':1,'actual_tool_chunk':'912386',
 'parent_pid':54132,'child_pid':12924,'actual_child_wait_exit_code':1,
 'terminal_sha256':hashlib.sha256(raw).hexdigest(),
 'actual_elapsed_seconds':t['elapsed_seconds'],
 'actual_finished_at_UTC':t['finished_at_UTC'],
 'resource_limit_exceeded':True,'budget_expired':False,
 'PeakWorkingSetSize':t['max_observed_PeakWorkingSetSize'],
 'PeakPagefileUsage':t['max_observed_PeakPagefileUsage'],
 'cause':'Own runner stopped its retained child on the predeclared 7GiB peak-process-commit threshold. This is not an independent Lean mathematical rejection, OS OOM, or official verdict.',
 'separate_process_lookups':{'unprivileged_GetProcess_failed_tool_chunk':'75ff8a','escalated_after_terminal_lookup_tool_chunk':'3b8b37','escalated_query_returned_no_matching_parent_or_child':True},
 'compiler_resource_gate_passed':False,'official_submission_performed':False,
 'automatic_retry_performed':False,'goal_status':'active'}
out=Path(__file__).with_name('root-outer-observation.json')
assert not out.exists()
out.write_bytes((json.dumps(observation,indent=2)+'\n').encode())
p=root/'research-goal-20261016/direction-state.json'
j=json.loads(p.read_text(encoding='utf-8'))
assert j['last_review_number']==10 and j['main_rounds_since_review']==0
j['main_rounds_since_review']=1
j['previous_goal_turn_classification']='progress'
j['v8_resource_route'].update({'compiler_resource_run_status':'failed_resource_limit','compiler_resource_run_passed':False,'actual_outer_exit_code':1,'actual_child_exit_code':1,'actual_elapsed_seconds':t['elapsed_seconds'],'max_observed_PeakWorkingSetSize':t['max_observed_PeakWorkingSetSize'],'max_observed_PeakPagefileUsage':t['max_observed_PeakPagefileUsage']})
j['main_route']='The one v8 compiler-resource run actually stopped at its predeclared Windows peak-process-commit threshold (7.20GiB commit vs0.35GiB RSS). Preserve this exact failure; distinguish import mapping, thread-stack reservation and source compilation cost before selecting any next resource gate. Do not submit v8 on this failed gate.'
j['next_gate']='One static same-pin SDK/primary-source diagnosis of the large Windows commit-versus-RSS discrepancy, inherited --tstack=262144 and import/mapping behavior. No compiler retry, budget/threshold increase, new source/checker/numerical family or website upload until written review selects a concrete justified gate.'
j['resource_diagnostic_round_v8']={'started_UTC':'2026-10-20T14:08:08Z','review':10,'counter_transition':[0,1],'reason':'Actual v8 resource failure changes the diagnostic route; previous single compile gate ended.','compiler_retry_authorized':False}
p.write_bytes((json.dumps(j,ensure_ascii=False,indent=2)+'\n').encode())
prefix=('14:08:08Z实际终态覆盖下方running：原resource session72573真实outerexit1（tool912386），child12924因预定7GiB PeakPagefileUsage线由ownrunner停止，elapsed663.234s、RSS峰375066624B、commit峰7728263168B，terminalSHA b9e50233b9a50ecd9dd14945e2cce321d70d70ef05fec62fd6bcb4a1a001a162。不是3200timeout、数学拒绝或官网OOM；新C/olean/ilean未完成，不得提交v8或改flag冒充PASS。现启动宏观010后第1实际新诊断轮counter0→1，先静态核Windows提交内存与驻留内存差距、继承--tstack=262144及import/mmap路径；不自动重试/加预算/加阈值，不改冻结源。官网完整无条件目标、双内核/接受/推广及Git一致保留，goal active。\n\n')
for name in ['research-goal-20261016/DIRECTION.zh.md','research-goal-20261020-w9a2-runtime/CONTINUATION.zh.md']:
    q=root/name
    q.write_bytes(prefix.encode('utf-8')+q.read_bytes())
print(json.dumps({'actual_outer_exit_code':1,'resource_gate_passed':False,'review':10,'counter':1}))
