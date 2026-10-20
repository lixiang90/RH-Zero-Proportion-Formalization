from pathlib import Path
import hashlib
import json

root=Path(__file__).resolve().parents[1]
work=root/'tmp/w9a2-20261020/v8-resource-v1'
started=json.loads((work/'started.json').read_bytes())
child=json.loads((work/'child.json').read_bytes())
assert child['parent_pid']==54132 and child['child_pid']==12924
assert started['source']['sha256']=='5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b'
receipt={'schema':'root-v8-resource-run-actual-start-v1',
 'provenance':'Original exec tool returned a running session and a real own-child memory sample; started/child files corroborate the process identity.',
 'outer_original_session_id':72573,'outer_start_tool_chunk':'84e6a3',
 'actual_outer_exit_code':None,'actual_status':'running_at_start_observation',
 'parent_pid':child['parent_pid'],'child_pid':child['child_pid'],
 'monotonic_t0':started['monotonic_t0'],'compiler_monotonic_started':child['monotonic_started'],
 'started_at_UTC':started['started_at_UTC'],
 'gate_sha256':'66a73d9996a332c5c8762cd24d25108fd96fcf3cc909b7ec7287bf90d2ee6f1c',
 'source_sha256':started['source']['sha256'],
 'gate_checkpoint_commit_prefix':'973bbd0',
 'gate_checkpoint_actual_push_exit_code':0,'gate_push_tool_chunk':'20dc0f',
 'first_actual_sample':{'elapsed_s':1.218,'child_pid':12924,'peak_RSS_MiB':3.13,'peak_commit_MiB':0.52,'final':False},
 'compiler_resource_gate_passed':False,'fullchain_or_official_acceptance':False,
 'scope':'One new v8 ordinary compiler/C-generation resource run. Await the same original outer handle; no exporter/CoreAudit/nanoda or old-source repeat.'}
out=Path(__file__).with_name('actual-start.json')
assert not out.exists()
out.write_bytes((json.dumps(receipt,indent=2)+'\n').encode())
p=root/'research-goal-20261016/direction-state.json'
j=json.loads(p.read_text(encoding='utf-8'))
assert j['last_review_number']==10 and j['main_rounds_since_review']==0
j['v8_resource_route'].update({'compiler_resource_run_started':True,'compiler_resource_run_status':'running','original_outer_session_id':72573,'parent_pid':54132,'child_pid':12924,'actual_outer_exit_code':None,'gate_sha256':receipt['gate_sha256']})
j['next_gate']='Wait for original resource session72573 / parent54132 / child12924 actual terminal. Bind real child exit, three outputs, peak counters, exact input pins and real root outer exit before declaring compiler-resource PASS. No restart on observation timeout; no exporter/CoreAudit/nanoda. Official Linux full-chain acceptance still required.'
p.write_bytes((json.dumps(j,ensure_ascii=False,indent=2)+'\n').encode())
prefix=('v8单次resource编译已真正启动：原outer session72573、parent54132、child12924，t0='+str(started['monotonic_t0'])+'，gate66a73d9996a332c5c8762cd24d25108fd96fcf3cc909b7ec7287bf90d2ee6f1c。已收到真实内存采样，尚无child/parent终态或PASS；只等待原句柄，不重启。编译请求-o/-i/-c/--json，-M6500、7GiB ownchild峰值阈值、3200秒，无旧Candidate缓存，不跑export/CoreAudit/Nano。源码5424212b…/1829382B与新gate973bbd0已实际push；Windows测量仍非官方Linux全链等价。review10/counter0，这是同一门内执行等待，不增研究轮；goal active。\n\n')
for name in ['research-goal-20261016/DIRECTION.zh.md','research-goal-20261020-w9a2-runtime/CONTINUATION.zh.md']:
    q=root/name
    q.write_bytes(prefix.encode('utf-8')+q.read_bytes())
print(json.dumps({'recorded':'actual v8 resource run start','session':72573,'parent':54132,'child':12924,'t0':started['monotonic_t0']}))
