"""Freeze the completed single G production and unchanged failed replay."""
from pathlib import Path
from hashlib import sha256
import json
import os

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def pin(p):return sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def write(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def main():
    assert not (HERE/'files.json').exists() and not (HERE/'replay-attempt.json').exists()
    assert not (HERE/'independent-complete-replay.json').exists()
    preparation=load(HERE/'prepared-files.json')
    for row in preparation['files']:
        p=ROOT/row['path'];assert pin(p)==row['sha256'] and p.stat().st_size==row['bytes']
    result=load(HERE/'classification.json');terminal=load(HERE/'terminal.json');prefix=load(HERE/'prefix.json')
    assert result['complete_range_classified'] is True and result['passed'] is True
    assert result['committed_cases']==prefix['committed_cases']==5635876
    assert result['counts']==prefix['counts'] and result['prefix_sha256']==pin(HERE/'prefix.json')
    assert terminal['child_launches']==1 and terminal['exit_code']==0 and terminal['limit_stop'] is None
    assert result['inputs_sha256_start']==result['inputs_sha256_end']
    for name,h in result['inputs_sha256_start'].items():assert pin(ROOT/name)==h
    identity={'argv':['C:/Python314/python.exe','research-goal-20261018-stageG-complete-classification/replay_complete.py','--write-receipt'],'cwd':str(ROOT)}
    write(HERE/'replay-attempt.json',{
        'schema':'G-unchanged-failed-independent-replay-attempt-v1','command':identity,
        'command_sha256':sha256(json.dumps(identity,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
        'tool_chunk':'59d4f2','exit_code':1,'wall_seconds':1.8446292,'replay_calls':1,
        'source_sha256':pin(HERE/'replay_complete.py'),'trace_sha256':pin(HERE/'replay-failure.txt'),
        'failed_stage':'Open committed proof stream handles; before frame/case verification',
        'error':"TypeError: 'WindowsPath' object is not subscriptable at ROOT[s['path']]",
        'certificate_receipt_written':False,'source_repaired':False,'automatic_retry':False,
        'independent_complete_certificate_replay_passed':False})
    files=[]
    for p in sorted(HERE.iterdir()):
        if p.is_file() and p.name!='files.json':
            files.append({'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)})
    dependencies=[{'path':name,'bytes':(ROOT/name).stat().st_size,'sha256':h}
        for name,h in sorted(result['inputs_sha256_start'].items()) if not name.startswith(HERE.name+'/')]
    out={'schema':'G-one-complete-fixed-production-with-failed-replay-package-v1','files':files,
        'read_only_dependencies':dependencies,'external_read_only_runtime':preparation['external_read_only_runtime'],
        'classification_executions':1,'child_launches':1,'complete_range_classified':True,
        'cases':result['committed_cases'],'counts':result['counts'],'replay_executions':1,
        'independent_complete_replay_passed':False,'failed_replay_unchanged':True,
        'unresolved_nonempty_claim':False,'new_global_joint_floor_proven':False,
        'new_unconditional_zero_proportion_proven':False,'website_source_and_runtime_budget':'unknown',
        'scope':'One complete fixed opportunity classification. All producer evidence retained. The unchanged built-in independent replay failed before certificate loop; no retry. Independent external mathematical review pending.'}
    write(HERE/'files.json',out)
    print(json.dumps({'manifest_sha256':pin(HERE/'files.json'),'files':len(files),
        'file_bytes':sum(x['bytes'] for x in files),'classification_complete':True,'independent_replay_passed':False}))
if __name__=='__main__':main()
