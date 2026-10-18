"""Freeze I output bytes and metadata endpoints only, no affine replay."""
from pathlib import Path
from hashlib import sha256
import json
import os

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
PREPARED='bf7c67dac30c1558b80ffa78b2e621555a1016f0b5ac18f4e87cd5cecf8874b7'
def pin(p):return sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)}
def write_new(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def main():
    assert not (HERE/'files.json').exists() and pin(HERE/'prepared-files.json')==PREPARED
    for rec in load(HERE/'prepared-files.json')['files']:
        p=ROOT/rec['path'];assert p.stat().st_size==rec['bytes'] and pin(p)==rec['sha256']
    result=load(HERE/'result.json');terminal=load(HERE/'terminal.json');started=load(HERE/'started.json')
    assert result['inputs_sha256_start']==result['inputs_sha256_end']==started['inputs_sha256']
    dependencies=[]
    for name,expected in sorted(result['inputs_sha256_end'].items()):
        p=(ROOT/name).resolve();assert p.is_relative_to(ROOT) and pin(p)==expected;dependencies.append(row(p))
    assert result['passed'] is True and result['arithmetic_evaluations']==1
    assert result['sample_G_index']==2417 and result['cell_ids']==[0,604] and result['chart']=='id/rev'
    assert result['point_unchanged'] is True and result['phase2_authorized'] is False
    assert terminal['exit_code']==0 and terminal['limit_stop'] is None and terminal['child_launches']==1
    files=[row(p) for p in sorted(HERE.iterdir()) if p.is_file() and p.name!='files.json']
    failures=[p.name for p in HERE.iterdir() if p.is_file() and ('failure' in p.name or 'inconclusive' in p.name)]
    manifest={'schema':'I-one-original-twoFS-fixed-point-producer-evidence-v1','files':files,
        'read_only_dependencies':dependencies,'prepared_manifest_sha256':PREPARED,
        'arithmetic_evaluations':1,'child_launches':1,'sample_G_index':2417,'chart':'id/rev','original_cells':[0,604],
        'result_sha256':pin(HERE/'result.json'),'all_owned_bytes_and_input_endpoints_verified':True,
        'all_failure_or_inconclusive_artifacts_preserved':failures,
        'affine_or_domain_replay_executed_by_freezer':False,'independent_arithmetic_review_pending':True,
        'producer_reported_delta':result['joint']['delta_integer'],
        'producer_reported_gap':result['joint']['sum_minus_twice_c'],
        'producer_reported_model_obstructed':result['joint']['fixed_two_FS_model_obstructed_at_sample'],
        'phase2_authorized':False,'matrix_basis_LP_newkernel_or_Lean_runs':0,
        'new_global_floor_or_unconditional_kappa_proven':False,'website_submission_ready':False,
        'scope':'Immutable raw producer evidence. Positive fixed-point gap is only a necessary opportunity, not a uniform lower bound.'}
    write_new(HERE/'files.json',manifest)
    print(json.dumps({'frozen_producer_only':True,'manifest':row(HERE/'files.json'),
        'owned_files':len(files),'owned_bytes':sum(x['bytes'] for x in files),'independent_review_pending':True}))

if __name__=='__main__':main()
