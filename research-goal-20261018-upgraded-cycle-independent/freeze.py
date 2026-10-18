"""Metadata-only freeze after the one fixed-nine-edge independent audit."""
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
    assert not (HERE/'audit-files.json').exists() and not (HERE/'execution.json').exists()
    assert not (HERE/'failure.json').exists()
    prep=load(HERE/'prepared-files.json')
    for row in prep['files']:
        p=ROOT/row['path'];assert pin(p)==row['sha256'] and p.stat().st_size==row['bytes']
    r=load(HERE/'independent-review.json');assert r['passed'] is True and r['independent_audit_calls']==1
    assert r['J_original_records_parsed_to_exact_EOF']==15378
    assert r['inputs_sha256_start']==r['inputs_sha256_end']
    for name,h in r['inputs_sha256_start'].items():assert pin(ROOT/name)==h
    command={'argv':['C:/Python314/python.exe','-B','-X','utf8',
        'research-goal-20261018-upgraded-cycle-independent/audit_cycle.py','--audit-authorized-fixed-cycle',
        '--gate','research-goal-20261016/gates/stageL-independent-upgraded-cycle-20261018.json',
        '--gate-sha256','b7b17e3a942e8bb07bbf6b9b79284e7a0a3f047ca28cc658853a28ddbaed6e23'],
        'cwd':str(ROOT)}
    stdout={'passed':True,'seconds':r['seconds'],'exact_sum':r['exact_upgraded_cycle_weight'],
        'fixed_outer_model_refuted':r['fixed_J_enhanced_outer_potential_model_refuted']}
    with (HERE/'stdout.log').open('x',encoding='utf-8',newline='\n') as f:f.write(json.dumps(stdout)+'\n')
    with (HERE/'stderr.log').open('xb') as f:pass
    write(HERE/'execution.json',{'schema':'one-fixed-nine-edge-independent-terminal-v1',
        'command':command,'command_sha256':sha256(json.dumps(command,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
        'pid':r['pid'],'tool_chunk':'a993b2','exit_code':0,'wall_seconds':1.2852054,
        'audit_seconds':r['seconds'],'audit_calls':1,'automatic_retry':False,
        'source_sha256':pin(HERE/'audit_cycle.py'),'receipt_sha256':pin(HERE/'independent-review.json'),
        'stdout_sha256':pin(HERE/'stdout.log'),'stderr_sha256':pin(HERE/'stderr.log'),
        'logs_are_UTF8_LF_tool_text_transcripts_not_raw_OS_pipe_bytes':True})
    files=[{'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)}
        for p in sorted(HERE.iterdir()) if p.is_file() and p.name!='audit-files.json']
    deps=[{'path':name,'bytes':(ROOT/name).stat().st_size,'sha256':h}
        for name,h in sorted(r['inputs_sha256_start'].items()) if not name.startswith(HERE.name+'/')]
    write(HERE/'audit-files.json',{'schema':'fixed-nine-J-upgraded-cycle-independent-package-v1',
        'files':files,'read_only_dependencies':deps,'passed':True,'audit_calls':1,
        'exact_upgraded_cycle_weight':r['exact_upgraded_cycle_weight'],
        'fixed_J_enhanced_outer_potential_model_refuted':r['fixed_J_enhanced_outer_potential_model_refuted'],
        'mixed_affine_other_bases_or_actual_F_refuted':False,'new_unconditional_zero_proportion_proven':False,
        'scope':'Only the unchanged nine-edge K cycle with fixed independently audited J upgrades; no FS/matrix/search or actual-energy claim.'})
    print(json.dumps({'manifest_sha256':pin(HERE/'audit-files.json'),'receipt_sha256':pin(HERE/'independent-review.json'),
        'pid':r['pid'],'files':len(files),'bytes':sum(x['bytes'] for x in files),'passed':True}))
if __name__=='__main__':main()
