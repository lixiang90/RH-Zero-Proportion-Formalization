"""Preserve a root-observed ordinary stage terminal; never changes round counters."""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]
ap=argparse.ArgumentParser()
ap.add_argument('--version',type=int,required=True)
ap.add_argument('--session',type=int,required=True)
ap.add_argument('--actual-exit',type=int,required=True)
ap.add_argument('--next-proof-gate',required=True)
args=ap.parse_args()
job=ROOT/f'tmp/w9a2-20261020/candidate-ordinary-v{args.version}'
terminal=json.loads((job/'terminal.json').read_text())
receipts=sorted(job.glob('*.receipt.json'))
assert receipts and args.actual_exit==(0 if terminal['passed'] else 1)
out=ROOT/f'research-goal-20261020-w9a2-ordinary-v{args.version}-terminal'
out.mkdir(exist_ok=False)
names=['started.json','terminal.json']
for p in receipts:
    stem=p.name.removesuffix('.receipt.json')
    names += [stem+'.'+s for s in ['command.json','child.json','log','receipt.json']]
rows=[]
for name in names:
    raw=(job/name).read_bytes();(out/name).write_bytes(raw)
    rows.append({'path':name,'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()})
attestation={'root_observed_parent_session':args.session,'actual_parent_exit_code':args.actual_exit,
    'source':'Root observed original exec session terminal, rather than inferred process disappearance',
    'at_UTC':datetime.now(timezone.utc).isoformat(),'job':job.relative_to(ROOT).as_posix(),
    'terminal_passed':terminal['passed'],'ordinary_only':True,'candidate_olean_reuse_development_only':True,
    'fullchain_passed':False,'submitted':False}
(out/'root-parent-exit-attestation.json').write_bytes((json.dumps(attestation,indent=2)+'\n').encode())
p=out/'root-parent-exit-attestation.json'
rows.append({'path':p.name,'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
(out/'files.json').write_bytes((json.dumps({'scope':'Actual ordinary stage terminal, not complete verification','files':rows},indent=2)+'\n').encode())
p=ROOT/'research-goal-20261016/direction-state.json'
state=json.loads(p.read_text(encoding='utf-8'));counter=state['main_rounds_since_review']
current=state['w9a2_current_round']
current.update(ordinary_session=args.session,ordinary_session_terminal_exit_code=args.actual_exit,
    currently_running_module=None,current_Lean_PID=None,next_proof_gate=args.next_proof_gate,
    ordinary_failure_preserved=out.relative_to(ROOT).as_posix())
status=[]
for p2 in receipts:
    r=json.loads(p2.read_text());name=r['module'].split('.')[-1]
    if r['ordinary_compile_passed']:
        current[name+'_ordinary_passed_seconds']=r['elapsed_seconds']
        current[name+'_olean_SHA256']=r['olean_sha256']
        status.append(name+' PASS '+str(round(r['elapsed_seconds'],3))+'s')
    else:
        current[name+'_ordinary_failed_seconds']=r['elapsed_seconds']
        status.append(name+' exit'+str(r['exit_code'])+' '+str(round(r['elapsed_seconds'],3))+'s')
assert state['main_rounds_since_review']==counter
p.write_bytes((json.dumps(state,ensure_ascii=False,indent=2)+'\n').encode())
paragraph=('\n\n同一macro007+round1实际ordinary-v'+str(args.version)+'原session'+str(args.session)+
    ' terminal exit'+str(args.actual_exit)+'：'+', '.join(status)+'。完整日志/命令/收据与root实际退出attestation已封'+
    out.name+'。下一proof关：'+args.next_proof_gate+'。未自动重试，counter保持'+str(counter)+
    '，完整验收与官网提交尚未发生。\n')
for rel in ['research-goal-20261016/DIRECTION.zh.md','research-goal-20261020-w9a2-runtime/CONTINUATION.zh.md']:
    p=ROOT/rel;p.write_bytes(p.read_bytes()+paragraph.encode())
print(json.dumps({'preserved':out.relative_to(ROOT).as_posix(),'parent_exit':args.actual_exit,'status':status,'counter':counter}))
