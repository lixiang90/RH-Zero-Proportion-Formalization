"""Freeze existing H evidence and input endpoints only; no certificate replay."""
from pathlib import Path
from hashlib import sha256
import json
import os

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
PREPARED='354293fdaa7051b33673bea458d9aca3d6db4339f1826a176998bffdcb25e682'
def pin(p):return sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)}
def write_new(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def main():
    assert not (HERE/'files.json').exists()
    assert pin(HERE/'prepared-files.json')==PREPARED
    for rec in load(HERE/'prepared-files.json')['files']:
        p=ROOT/rec['path'];assert p.stat().st_size==rec['bytes'] and pin(p)==rec['sha256']
    result=load(HERE/'result.json');prefix=load(HERE/'prefix.json');terminal=load(HERE/'terminal.json')
    assert result['inputs_sha256_start']==result['inputs_sha256_end']
    deps=[]
    for name,expected in sorted(result['inputs_sha256_end'].items()):
        p=(ROOT/name).resolve();assert p.is_relative_to(ROOT) and pin(p)==expected;deps.append(row(p))
    assert result['prefix_sha256']==pin(HERE/'prefix.json')
    assert terminal['published_prefix_sha256']==result['prefix_sha256']
    assert terminal['child_launches']==result['classification_passes']==1
    assert terminal['exit_code']==0 and terminal['limit_stop'] is None
    assert result['passed'] is True and result['complete_G_unresolved_classification'] is True
    assert result['committed_records']==prefix['committed_records']==19838
    assert result['counts']==prefix['counts'] and sum(prefix['counts'].values())==19838
    for name,countkey,hashkey in [('certificates.bin','committed_bytes','certificate_prefix_sha256'),
                                  ('remaining-indices.u32.bin','committed_remaining_bytes','remaining_indices_prefix_sha256')]:
        p=HERE/name;assert p.stat().st_size==prefix[countkey] and pin(p)==prefix[hashkey]
    files=[row(p) for p in sorted(HERE.iterdir()) if p.is_file() and p.name!='files.json']
    failures=[p.name for p in HERE.iterdir() if p.is_file() and ('failure' in p.name or 'inconclusive' in p.name)]
    manifest={'schema':'H-one-fixed-G-unresolved-producer-evidence-v1','files':files,'read_only_dependencies':deps,
        'prepared_manifest_sha256':PREPARED,'classification_passes':1,'child_launches':1,
        'complete_G_unresolved_classification':True,'records':19838,'counts_producer_only':result['counts'],
        'result_sha256':pin(HERE/'result.json'),'prefix_sha256':pin(HERE/'prefix.json'),
        'input_endpoints_and_all_owned_file_bytes_verified':True,'certificate_replay_executed_by_freezer':False,
        'all_failure_or_inconclusive_artifacts_preserved':failures,'independent_audit_pending':True,
        'LP_calls':0,'new_FS_kernel_points_or_Lean_runs':0,'new_global_joint_floor_proven':False,
        'new_unconditional_zero_proportion_proven':False,'website_submission_ready':False,
        'scope':'Immutable raw producer evidence only. No independent Empty certificate replay or complete actual floor claim.'}
    write_new(HERE/'files.json',manifest)
    print(json.dumps({'frozen_producer_only':True,'manifest':row(HERE/'files.json'),
                      'owned_files':len(files),'owned_bytes':sum(x['bytes'] for x in files),
                      'counts':result['counts'],'independent_audit_pending':True}))

if __name__=='__main__':main()
