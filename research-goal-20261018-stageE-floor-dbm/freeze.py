"""Freeze terminal E and closed witness replay; no additional model checking."""
from pathlib import Path
from hashlib import sha256
import gzip
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def pin(p):return sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)}

def main():
    out=HERE/'files.json';assert not out.exists()
    a=load(HERE/'model.json');t=load(HERE/'terminal.json');r=load(HERE/'independent-witness-replay.json')
    assert a['passed'] and r['passed'] and t['exit_code']==0 and t['limit_stop'] is None
    assert a['model_passes']==t['child_launches']==1
    assert a['cases_checked']==r['cases_checked']==1193
    assert a['outcome']==r['outcome']=='underpaid_relaxed_DBM_feasible_ordered_violated'
    assert a['counts']==r['counts']=={'original_scalar_floors_pay_target':766,
        'underpaid_shared_span_two_edge_conflict':426,'underpaid_feasible_case':1}
    assert not a['all_cases_covered'] and a['stopped_at_first_underpaid_relaxed_feasible']
    assert a['inputs_sha256_start']==a['inputs_sha256_end']
    refs=[]
    for name,expected in a['inputs_sha256_start'].items():
        p=ROOT/name;assert pin(p)==expected
        if p.parent!=HERE:refs.append(row(p))
    payload=gzip.decompress((HERE/'witness-prefix.bin.gz').read_bytes())
    assert len(payload)==2050 and sha256(payload).hexdigest()==a['proof_stream']['uncompressed_sha256']
    files=[row(p) for p in sorted(HERE.iterdir()) if p.is_file() and p.name!='files.json']
    assert sum(r['bytes'] for r in files)<20000000
    result={'schema':'fixed-exact-margin-and-DBM-E-opportunity-package-v1','files':files,
        'total_bytes':sum(r['bytes'] for r in files),'read_only_dependencies':sorted(refs,key=lambda x:x['path']),
        'model_passes':1,'child_exit_code':0,'cases_checked':1193,'total_cases':5635876,
        'counts':a['counts'],'outcome':a['outcome'],'all_cases_covered':False,
        'stopped_at_first_underpaid_feasible':True,'both_ordered_conditions_violated':True,
        'own_independent_algorithm_witness_replay_passed':True,'other_agent_independent_review_pending':True,
        'scope':'Exact original scalar floors plus unchanged relaxed geometry did not close; first underpaid DBM point violates Ordered. Not actual low energy or a counterexample.',
        'new_kernel_queries':0,'optimizer_calls':0,'Lean_runs':0,'new_joint_floor_proven':False,
        'new_unconditional_zero_proportion_proven':False,'website_submission_ready':False,
        'complete_source_and_runtime_budget':'unknown','mutable_governance_dependency':False}
    with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps({'path':out.relative_to(ROOT).as_posix(),'sha256':pin(out),'files':len(files),'total_bytes':result['total_bytes']}))

if __name__=='__main__':main()
