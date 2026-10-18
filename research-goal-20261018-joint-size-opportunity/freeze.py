"""Freeze closed integer count audit. No geometry or additional pair loop."""
from pathlib import Path
from hashlib import sha256
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def pin(p):return sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)}

def main():
    out=HERE/'files.json';assert not out.exists()
    a=load(HERE/'audit.json');t=load(HERE/'terminal.json')
    assert a['passed'] and t['exit_code']==0 and t['limit_stop'] is None
    assert a['audit_executions']==t['child_launches']==1
    assert not (HERE/'failure.json').exists()
    assert a['inputs_sha256_start']==a['inputs_sha256_end']
    assert a['underpaid_per_left_cell']==a['underpaid_per_right_cell']
    assert sum(a['underpaid_per_left_cell'])==a['underpaid_ordered_pairs_per_orientation']==881796
    assert a['scalar_paid_ordered_pairs_per_orientation']==527173
    assert a['scalar_paid_oriented_cases']+a['underpaid_oriented_cases']==5635876
    refs=[]
    for name,expected in a['inputs_sha256_end'].items():
        p=ROOT/name;assert pin(p)==expected
        if p.parent!=HERE:refs.append(row(p))
    files=[row(p) for p in sorted(HERE.iterdir()) if p.is_file() and p.name!='files.json']
    assert sum(r['bytes'] for r in files)<2000000
    result={'schema':'fixed-B-margin-size-opportunity-package-v1','files':files,
        'total_bytes':sum(r['bytes'] for r in files),'read_only_dependencies':sorted(refs,key=lambda x:x['path']),
        'audit_executions':1,'child_exit_code':0,'sorted_bisect_and_independent_integer_quadratic_counts_equal':True,
        'scalar_paid_oriented_cases':2108692,'underpaid_oriented_cases':3527184,'all_oriented_cases':5635876,
        'geometry_queries':0,'FS_queries':0,'kernel_queries':0,'new_points':0,'optimizer_calls':0,'Lean_runs':0,
        'scope':'Fixed existing integer margin multiset size audit only; no pair geometry or energy conclusion.',
        'full_source_and_runtime_budget':'unknown','new_joint_floor_proven':False,
        'new_unconditional_zero_proportion_proven':False,'website_submission_ready':False,
        'mutable_governance_dependency':False}
    with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps({'path':out.relative_to(ROOT).as_posix(),'sha256':pin(out),
        'files':len(files),'total_bytes':result['total_bytes']}))

if __name__=='__main__':main()
