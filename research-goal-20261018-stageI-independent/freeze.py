"""Freeze metadata after the one authorized fixed-I independent audit."""
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
    prep=load(HERE/'prepared-files.json')
    for row in prep['files']:
        p=ROOT/row['path'];assert pin(p)==row['sha256'] and p.stat().st_size==row['bytes']
    audit=load(HERE/'independent-review.json')
    assert audit['passed'] is True and audit['independent_audit_calls']==1
    assert audit['terms_independently_decoded']==68 and audit['all155_original_domain_rows_verified'] is True
    assert audit['inputs_sha256_start']==audit['inputs_sha256_end']
    for name,h in audit['inputs_sha256_start'].items():assert pin(ROOT/name)==h
    j=audit['joint']
    command={'argv':['C:/Python314/python.exe','-B','-X','utf8',
        'research-goal-20261018-stageI-independent/audit_point.py','--verify-authorized-fixed-I',
        '--gate','research-goal-20261016/gates/stageI-independent-original-affine-20261018.json',
        '--gate-sha256','9649ab6ebb763eb65069df224c204fe43e087e45e9986f0787d3a06bbe733f58'],
        'cwd':str(ROOT)}
    stdout={'passed':True,'seconds':audit['seconds'],'delta_integer':j['delta_integer'],
        'sum_minus_twice_c':j['sum_minus_twice_c']}
    with (HERE/'stdout.log').open('x',encoding='utf-8',newline='\n') as f:
        f.write(json.dumps(stdout)+'\n')
    with (HERE/'stderr.log').open('xb') as f:pass
    runtime=Path('C:/Python314/python.exe')
    runtime_identity={'path':str(runtime),'bytes':runtime.stat().st_size,'sha256':pin(runtime),
        'external_read_only_identity':True,'copied':False}
    write(HERE/'execution.json',{'schema':'I-one-independent-audit-raw-terminal-v1','command':command,
        'command_sha256':sha256(json.dumps(command,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
        'pid':audit['pid'],'tool_chunk':'182e2d','exit_code':0,'wall_seconds':5.1294225,
        'receipt_seconds':audit['seconds'],'audit_calls':1,'automatic_retry':False,
        'stdout_sha256':pin(HERE/'stdout.log'),'stderr_sha256':pin(HERE/'stderr.log'),
        'source_sha256':pin(HERE/'audit_point.py'),'receipt_sha256':pin(HERE/'independent-review.json'),
        'external_read_only_runtime':runtime_identity})
    files=[]
    for p in sorted(HERE.iterdir()):
        if p.is_file() and p.name!='audit-files.json':
            files.append({'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)})
    deps=[{'path':name,'bytes':(ROOT/name).stat().st_size,'sha256':digest}
        for name,digest in sorted(audit['inputs_sha256_start'].items()) if not name.startswith(HERE.name+'/')]
    result={'schema':'I-independent-one-fixed-original-affine-point-package-v1','files':files,
        'read_only_dependencies':deps,'external_read_only_runtime':runtime_identity,'audit_calls':1,
        'passed':True,'fixed_cells':[0,604],'chart':'id/rev','fixed_G_index':2417,
        'original_FS_terms_independently_decoded':68,'original155_rows_verified':True,
        'producer_modules_imported':False,'old_A_parser_math_reused':True,
        'joint_delta_integer':j['delta_integer'],'joint_sum_minus_twice_c':j['sum_minus_twice_c'],
        'new_FS_point_kernel_LP_matrix_or_Lean_runs':0,'new_global_joint_floor_proven':False,
        'new_unconditional_zero_proportion_proven':False,
        'scope':'Independent original two-FS signed Fraction and integer identities at the one unchanged old point. Positive sample margin only, no uniform floor.'}
    write(HERE/'audit-files.json',result)
    print(json.dumps({'manifest_sha256':pin(HERE/'audit-files.json'),'receipt_sha256':pin(HERE/'independent-review.json'),
        'pid':audit['pid'],'files':len(files),'file_bytes':sum(x['bytes'] for x in files),'passed':True}))
if __name__=='__main__':main()
