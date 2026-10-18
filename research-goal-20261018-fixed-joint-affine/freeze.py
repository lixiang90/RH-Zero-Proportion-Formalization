"""Freeze completed D. Only hash/closed scalar identities; no term reevaluation."""
from pathlib import Path
from hashlib import sha256
from fractions import Fraction as F
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def pin(p):return sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text(encoding='utf-8'))
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)}

def main():
    out=HERE/'files.json';assert not out.exists()
    a=read(HERE/'evaluation.json');terminal=read(HERE/'terminal.json')
    assert a['passed'] and terminal['exit_code']==0 and terminal['limit_stop'] is None
    assert a['arithmetic_passes']==terminal['child_launches']==1
    assert not (HERE/'failure.json').exists()
    assert a['inputs_sha256_start']==a['inputs_sha256_end']
    deps=[]
    for name,expected in a['inputs_sha256_start'].items():
        p=ROOT/name;assert pin(p)==expected
        if p.parent!=HERE:deps.append(row(p))
    assert F(a['sum_minus_twice_c'])==F(a['clipped_sum_minus_twice_c'])>0
    marginbudget=[]
    kappa=a['scales']['KAPPA'];SA=a['scales']['SA'];cnum=a['target_c_numerator']
    c9num=893616123055294719;target=kappa*(cnum-c9num)
    for w in a['windows']:
        m=int(w['original_compact_margin']);floor=F(c9num,SA)+F(m,kappa*SA)
        assert floor==F(w['original_flow']['certified_affine_floor'])
        assert F(w['affine_value_at_fixed_point'])>=floor>=F(cnum,SA)
        marginbudget.append({'offset':w['offset'],'original_M0':str(m),
            'kappa_times_target_increment':str(target),'integer_surplus':str(m-target),
            'existing_certified_floor':str(floor),'at_least_target_c_on_original_cell':True})
    files=[row(p) for p in sorted(HERE.iterdir()) if p.is_file() and p.name!='files.json']
    assert sum(r['bytes'] for r in files)<8000000
    manifest={'schema':'fixed-C-point-two-original-FS-affine-diagnostic-package-v1',
        'files':files,'total_bytes':sum(r['bytes'] for r in files),
        'read_only_dependencies':sorted(deps,key=lambda x:x['path']),
        'arithmetic_passes':1,'other_agent_independent_review_pending':True,
        'raw_and_clipped_point_margin_positive':True,'existing_original_margin_budget':marginbudget,
        'no_whole_pair_campaign_or_solver_started':True,
        'scope':'One fixed rational point and two unchanged FS affine expressions. Original per-cell margin proof also already pays this pair; no assertion for other exception pairs.',
        'new_kernel_queries':0,'optimizer_calls':0,'Lean_runs':0,
        'new_joint_floor_proven':False,'new_unconditional_zero_proportion_proven':False,
        'complete_source_and_runtime_budget':'unknown','website_submission_ready':False,
        'mutable_governance_dependency':False}
    with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(manifest,f,indent=2);f.write('\n')
    print(json.dumps({'path':out.relative_to(ROOT).as_posix(),'sha256':pin(out),
        'files':len(files),'total_bytes':manifest['total_bytes'],'existing_margin_budget':marginbudget}))

if __name__=='__main__':main()
