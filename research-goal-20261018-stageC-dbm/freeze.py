"""Freeze this terminal bounded scan and its witness; no additional scan."""
from pathlib import Path
from hashlib import sha256
import gzip
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def pin(p):return sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text(encoding='utf-8'))
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':pin(p)}

def main():
    out=HERE/'files.json';assert not out.exists()
    a=read(HERE/'scan.json');terminal=read(HERE/'terminal.json');r=read(HERE/'independent-cycle-replay.json')
    assert a['passed'] and terminal['exit_code']==0 and terminal['limit_stop'] is None
    assert terminal['child_launches']==a['scan_passes']==1 and r['passed']
    assert a['cases_checked']==r['cases_checked']==2
    assert a['outcome']==r['outcome']=='ordered_conditions_hold'
    assert not a['all_cases_covered'] and a['stopped_at_first_relaxed_feasible']
    assert a['inputs_sha256_start']==a['inputs_sha256_end']
    dependencies=[]
    for name,expected in a['inputs_sha256_start'].items():
        p=ROOT/name;assert pin(p)==expected
        if p.parent!=HERE:dependencies.append(row(p))
    proof=HERE/'cycle-prefix.bin.gz';payload=gzip.decompress(proof.read_bytes())
    assert payload==bytes([82,90,68,66,77,49,10,2,98,41,240])
    assert sha256(payload).hexdigest()==a['proof_stream']['uncompressed_sha256']
    files=[row(p) for p in sorted(HERE.iterdir()) if p.is_file() and p.name!='files.json']
    assert sum(r['bytes'] for r in files)<20000000
    data={'schema':'fixed-four-orientation-DBM-opportunity-package-v1','files':files,
        'total_bytes':sum(r['bytes'] for r in files),
        'read_only_dependencies':sorted(dependencies,key=lambda r:r['path']),
        'scan_passes':1,'child_exit_code':0,'cases_checked':2,'total_possible_cases':5635876,
        'outcome':'ordered_conditions_hold','full_scan_completed':False,
        'first_relaxed_feasible_stopped_scan':True,'all153_edges_verified':True,
        'local_independent_algorithm_witness_replay_passed':True,
        'other_agent_independent_review_pending':True,
        'scope':'Fixed unchanged B outer cells admit an adjacent DBM point with both ordered conditions. This is not actual low energy or a counterexample to the candidate floor.',
        'new_kernel_queries':0,'optimizer_calls':0,'Lean_runs':0,
        'new_joint_floor_proven':False,'new_unconditional_zero_proportion_proven':False,
        'complete_source_and_runtime_budget':'unknown','complete_source_gate_passed':False,
        'website_submission_ready':False,'mutable_governance_dependency':False}
    with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(data,f,indent=2);f.write('\n')
    print(json.dumps({'path':out.relative_to(ROOT).as_posix(),'sha256':pin(out),
        'files':len(files),'total_bytes':data['total_bytes']}))

if __name__=='__main__':main()
