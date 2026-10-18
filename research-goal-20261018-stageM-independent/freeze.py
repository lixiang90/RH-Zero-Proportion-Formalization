"""Metadata-only immutable freeze after the single M independent audit."""
from pathlib import Path
from hashlib import sha256
import json
import os
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def pin(p):return sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def write(path,obj):
    with path.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(obj,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def main():
    assert not (HERE/'audit-files.json').exists() and not (HERE/'execution.json').exists()
    assert not (HERE/'failure.json').exists()
    prepared=load(HERE/'prepared-files.json')
    for item in prepared['files']:
        p=ROOT/item['path'];assert p.stat().st_size==item['bytes'] and pin(p)==item['sha256']
    audit=load(HERE/'independent-review.json')
    assert audit['passed'] is True and audit['independent_audit_calls']==1
    assert audit['variables']==77 and audit['full_dual_coordinates']==78 and audit['rows']==279
    assert audit['valid_local_Lower'] is True and audit['valid_fixed_model_Below'] is False
    assert audit['exact_primal_dual_objectives_equal_if_both_valid'] is True
    assert audit['inputs_sha256_start']==audit['inputs_sha256_end']
    for name,h in audit['inputs_sha256_start'].items():assert pin(ROOT/name)==h
    for item in prepared['external_audit_runtime']:
        p=Path(item['path']);assert p.stat().st_size==item['bytes'] and pin(p)==item['sha256']
    for name,h in audit['external_discovery_runtime_sha256'].items():assert pin(Path(name))==h
    command={'argv':['C:/Python314/python.exe','-B','-X','utf8',
        'research-goal-20261018-stageM-independent/audit_certificate.py','--audit-authorized-fixed-M',
        '--gate','research-goal-20261016/gates/stageM-independent-component-20261018.json',
        '--gate-sha256','94963606d012335c9317f0b1a9e0848038399631836b8b9d98daa1044d8e4150'],
        'cwd':str(ROOT)}
    stdout={'passed':True,'rows':279,'valid_local_Lower':True,'valid_fixed_model_Below':False,'seconds':audit['seconds']}
    with (HERE/'stdout.log').open('x',encoding='utf-8',newline='\n') as f:f.write(json.dumps(stdout)+'\n')
    with (HERE/'stderr.log').open('xb') as f:pass
    write(HERE/'execution.json',{'schema':'M-one-independent-audit-terminal-v1','pid':audit['pid'],
        'command':command,'command_sha256':sha256(json.dumps(command,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
        'tool_chunk':'280681','exit_code':0,'wall_seconds':4.5329365,'audit_seconds':audit['seconds'],
        'audit_calls':1,'automatic_retry':False,'source_sha256':pin(HERE/'audit_certificate.py'),
        'receipt_sha256':pin(HERE/'independent-review.json'),'stdout_sha256':pin(HERE/'stdout.log'),
        'stderr_sha256':pin(HERE/'stderr.log'),'logs_are_UTF8_LF_tool_transcripts_not_raw_OS_pipe_bytes':True})
    files=[{'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)}
        for p in sorted(HERE.iterdir()) if p.is_file() and p.name!='audit-files.json']
    deps=[{'path':name,'bytes':(ROOT/name).stat().st_size,'sha256':h}
        for name,h in sorted(audit['inputs_sha256_start'].items()) if not name.startswith(HERE.name+'/')]
    write(HERE/'audit-files.json',{'schema':'M-independent-fixed-component-Lower-package-v1','files':files,
        'read_only_dependencies':deps,'external_audit_runtime':prepared['external_audit_runtime'],
        'external_discovery_runtime_sha256':audit['external_discovery_runtime_sha256'],
        'passed':True,'audit_calls':1,'fixed_cells':[0,604],'chart':'id/rev','rows':279,'variables':77,
        'full78_exact_dual_valid':True,'all_raw_primal_rows_valid':True,'exact_primal_dual_objectives_equal':True,
        'raw_surplus':audit['dual_checks']['raw_minus_target'],'new_global_floor_or_unconditional_kappa_proven':False,
        'scope':'One independently reconstructed original-component polyhedral Lower only. Original analytic soundness and a new actual Lean consumer remain separate; no whole-domain or website acceptance claim.'})
    print(json.dumps({'manifest_sha256':pin(HERE/'audit-files.json'),'receipt_sha256':pin(HERE/'independent-review.json'),
        'pid':audit['pid'],'files':len(files),'bytes':sum(r['bytes'] for r in files),'passed':True}))
if __name__=='__main__':main()
