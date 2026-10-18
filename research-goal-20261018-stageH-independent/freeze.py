"""Metadata-only freeze after the one authorized independent H audit."""
from pathlib import Path
from hashlib import sha256
import json
import os

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def pin(p):return sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def write(p,data):
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(data,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def main():
    assert not (HERE/'audit-files.json').exists() and not (HERE/'execution.json').exists()
    assert not (HERE/'failure.json').exists()
    prepared=load(HERE/'prepared-files.json')
    for row in prepared['files']:
        p=ROOT/row['path'];assert pin(p)==row['sha256'] and p.stat().st_size==row['bytes']
    review=load(HERE/'independent-review.json')
    assert review['passed'] is True and review['complete_input_range_processed'] is True
    assert review['records']==19838 and review['counts']=={'Empty':4460,'unresolved':15378}
    assert review['every_claimed_Empty_full10_balance_and_strict_cost_verified'] is True
    assert review['inputs_sha256_start']==review['inputs_sha256_end']
    for name,digest in review['inputs_sha256_start'].items():assert pin(ROOT/name)==digest
    command={'argv':['C:/Python314/python.exe','research-goal-20261018-stageH-independent/audit_h.py',
        '--verify-authorized-H-result','--gate','research-goal-20261016/gates/stageH-ordered-transport-20261018.json',
        '--gate-sha256','2533ebb71be8f21d3ce9306a54e12250229b962974f6f86e2a02b450eb977eb9',
        '--producer-manifest','research-goal-20261018-stageH-ordered-transport/files.json',
        '--producer-manifest-sha256','327562525e30d7b706777e71af003e51ca93a218ac7cfd9bfa0994abe56f8f8c',
        '--write-receipt'],'cwd':str(ROOT)}
    write(HERE/'execution.json',{'schema':'H-one-independent-audit-terminal-v1','command':command,
        'command_sha256':sha256(json.dumps(command,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
        'tool_chunk':'8e2b20','exit_code':0,'wall_seconds':3.6781362,
        'receipt_seconds':review['seconds'],'mathematical_audit_calls':1,'automatic_retry':False,
        'source_sha256':pin(HERE/'audit_h.py'),'receipt_sha256':pin(HERE/'independent-review.json'),
        'python_pid_not_recorded_by_direct_CLI':True,
        'stdout':{'passed':True,'complete_input_range_processed':True,
            'counts':{'Empty':4460,'unresolved':15378},'records':19838,'seconds':review['seconds']}})
    files=[]
    for p in sorted(HERE.iterdir()):
        if p.is_file() and p.name!='audit-files.json':
            files.append({'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)})
    deps=[{'path':name,'bytes':(ROOT/name).stat().st_size,'sha256':digest}
        for name,digest in sorted(review['inputs_sha256_start'].items()) if not name.startswith(HERE.name+'/')]
    manifest={'schema':'H-independent-original155row-full-prefix-audit-package-v1',
        'files':files,'read_only_dependencies':deps,
        'external_read_only_runtime':prepared['external_read_only_runtime'],
        'mathematical_audit_calls':1,'complete_input_range_processed':True,'records':19838,
        'counts':review['counts'],'every_Empty_full10_balance_and_strict_integer_cost_verified':True,
        'producer_modules_imported':0,'discovery_or_optimization_calls':0,
        'unresolved_nonempty_claimed':False,'new_global_joint_floor_proven':False,
        'new_unconditional_zero_proportion_proven':False,'whole_source_and_policy_runtime_budget':'unknown',
        'scope':'One complete independent audit of supplied H original155row integer Empty certificates only; unresolved remains open, no new discovery or actual-energy claim.'}
    write(HERE/'audit-files.json',manifest)
    print(json.dumps({'manifest_sha256':pin(HERE/'audit-files.json'),'receipt_sha256':pin(HERE/'independent-review.json'),
        'files':len(files),'file_bytes':sum(r['bytes'] for r in files),'passed':True,'audit_calls':1}))
if __name__=='__main__':main()
