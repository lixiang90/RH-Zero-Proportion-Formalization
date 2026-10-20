"""Record the reviewed Graph repair and direct human submission authorization."""
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parents[1]
p=ROOT/'research-goal-20261016/direction-state.json'
s=json.loads(p.read_text(encoding='utf-8'))
assert s['main_rounds_since_review']==1 and s['last_review_number']==7
s['w9a2_current_round'].update(
    ordinary_gate='research-goal-20261016/gates/w9a2-ordinary-v2-20261020.json',
    ordinary_gate_SHA256='59062ce669fcfc8e8a18e3367688f3f9e7d0eb8e9e1120fdbc2ab12f3ff57dac',
    ordinary_session=42867,ordinary_session_terminal_exit_code=None,
    currently_running_module='Graph',current_Lean_PID=1604,
    graph_repair_manifest='research-goal-20261020-w9a2-graph-repair-v1/files.json',
    graph_repair_manifest_SHA256='a7a9b9090f51919d3f07276a758e333fed135f98a7b854dbe84f755bc4f0de19',
    next_proof_gate='Complete Graph/Localization/Counting/Final, then final regenerated single-file and full kernel/budget verification')
s['website_submission_authorization']={
    'source':'Direct human steering within the same research round',
    'instruction':'我已登录，请在完成验证后提交，姓名填写Li Xiang',
    'destination':'https://www.riemannzeta.fun/submit',
    'public_author_name':'Li Xiang',
    'submit_after_complete_verification':True,
    'additional_confirmation_required':False,
    'login_status':'User reports logged in; root will verify visible page before submission',
    'submitted':False}
s['remaining_required_work'][-1]='Deliver complete submission materials, submit verified exact source as Li Xiang under direct human authorization, and verify official website acceptance'
p.write_bytes((json.dumps(s,ensure_ascii=False,indent=2)+'\n').encode())
paragraph=('\n\n同一macro007+round1收到用户明确指示：已登录，完成验证后直接提交官网，姓名Li Xiang。'
           '这已授权最终合格源码提交，无需再确认；实际提交与正式接受仍未发生。'
           'Graph repair a7a9b909…仅reverse_span证明行增加独立Fin.reduceFinMk化简+32B，'
           'gate59062ce6…/唯一session42867 child1604已运行Graph→Localization→Counting→Final，'
           '开发只复用已PASS的同SHA Prefix/Core。count仍1，轮内用户steering不增轮。\n')
for rel in ['research-goal-20261016/DIRECTION.zh.md','research-goal-20261020-w9a2-runtime/CONTINUATION.zh.md']:
    p=ROOT/rel;p.write_bytes(p.read_bytes()+paragraph.encode())
print(json.dumps({'active_session':42867,'counter':1,'author':'Li Xiang','submission_authorized_after_verification':True}))
