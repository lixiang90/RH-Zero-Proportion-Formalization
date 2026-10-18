"""Byte-only freeze of the sole terminal N attempt; no mathematical replay."""
from pathlib import Path
from hashlib import sha256
import json
import os
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
PREPARED='ce7fdca4ebbce2e82fb915c1f1a3892dec362bff5e4ff8e74ef73de8aa854bd7'
GATE='research-goal-20261016/gates/stageN-complete-pooled-component-20261018.json'
GATE_SHA='8bc67b572594e68af94a2f6ebac787942f7a061d7c7167bb8c8eb38ab5223d09'
def pin(p,limit=None):
    h=sha256();left=limit
    with p.open('rb') as f:
        while left is None or left:
            b=f.read(1048576 if left is None else min(1048576,left))
            if not b:break
            h.update(b)
            if left is not None:left-=len(b)
    assert left in (None,0)
    return h.hexdigest()
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)}
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def write(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def main():
    assert not (HERE/'files.json').exists() and not (HERE/'freeze-receipt.json').exists()
    assert pin(HERE/'prepared-files.json')==PREPARED and pin(ROOT/GATE)==GATE_SHA
    prep=load(HERE/'prepared-files.json')
    for item in prep['files']:
        p=ROOT/item['path'];assert pin(p)==item['sha256'] and p.stat().st_size==item['bytes']
    terminal=load(HERE/'terminal.json');failure=load(HERE/'failure.json');prefix=load(HERE/'prefix.json')
    assert terminal['exit_code']==1 and terminal['child_launches']==1 and terminal['limit_stop'] is None
    assert terminal['inputs_unchanged_after_terminal'] and terminal['external_runtime_unchanged_after_terminal']
    assert failure['error'].startswith('PermissionError') and 'os.replace' in failure['traceback']
    assert prefix['committed_records']==675 and prefix['counts']=={'Lower':674,'deduction_Lower':1}
    assert failure['committed_records']==676 and failure['linprog_calls_started']==675
    prefixes=[]
    for name,desc in prefix['streams'].items():
        p=ROOT/desc['path'];assert p.name==name and pin(p,desc['bytes'])==desc['sha256']
        prefixes.append({'path':desc['path'],'committed_bytes':desc['bytes'],
            'committed_sha256':desc['sha256'],'full_file_bytes':p.stat().st_size,
            'full_file_sha256':pin(p),'unpublished_tail_bytes':p.stat().st_size-desc['bytes']})
    receipt={'schema':'N-terminal-byte-only-freeze-receipt-v1','passed_byte_identity_checks':True,
        'published_prefix_records':675,'published_counts':prefix['counts'],
        'in_memory_records_at_failure':676,'actual_linprog_calls_started':675,
        'session_id':1259,'parent_pid':47764,'child_pid':32868,'actual_child_exit_code':1,
        'failure_stage':failure['stage'],'failure_kind':'Windows os.replace permission failure',
        'prefix_bytes':prefixes,'prefix_sha256':pin(HERE/'prefix.json'),
        'pending_prefix_tmp_sha256':pin(HERE/'prefix.json.tmp'),
        'prepared_manifest_sha256':PREPARED,'gate_path':GATE,'gate_sha256':GATE_SHA,
        'mathematical_replay_executions':0,'source_or_parameter_changes':0,'automatic_retry':False,
        'whole_range_complete':False,'independent_mathematical_replay_pending':True,
        'unconditional_global_floor_or_submission_proven':False}
    write(HERE/'freeze-receipt.json',receipt)
    owned=[p for p in sorted(HERE.iterdir()) if p.is_file() and p.name!='files.json']
    manifest={'schema':'N-sole-attempt-failure-and-durable-prefix-package-v1','files':[row(p) for p in owned],
        'read_only_dependencies':prep['read_only_dependencies']+[row(ROOT/GATE)],
        'external_read_only_runtime_files':prep['external_read_only_runtime_files'],
        'source_prepared_manifest_sha256':PREPARED,'published_records':675,'mathematical_replay_executions':0,
        'attempt_terminal':True,'whole_range_complete':False,'automatic_retry':False,
        'scope':'Byte-preserved one attempt, storage failure; only committed prefix is accepted, mathematical audit pending.'}
    write(HERE/'files.json',manifest)
    print(json.dumps({'frozen':row(HERE/'files.json'),'owned_files':len(owned),
        'owned_bytes':sum(p.stat().st_size for p in owned),'published_records':675,'math_replay_runs':0}))
if __name__=='__main__':main()
