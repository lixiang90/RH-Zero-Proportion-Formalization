"""Freeze original failed producer and raw output; no solver/dual recovery."""
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
    failure=load(HERE/'failure.json');terminal=load(HERE/'terminal.json');closed=load(HERE/'failure-closure.json')
    assert failure['stage']=='validate_primary_primal_dual' and failure['simplex_calls_started']==1
    assert terminal['exit_code']==1 and terminal['child_launches']==1 and terminal['limit_stop'] is None
    assert terminal['primary_call_marker_present'] and not terminal['conditional_auxiliary_call_marker_present']
    assert closed['outcome']=='inconclusive_failed_primal_validation'
    assert closed['primary_simplex_calls_returned']==1 and closed['auxiliary_simplex_calls']==0
    assert closed['certificate_verifier_invocations']==0 and closed['returned_primal_violated_row_count']==38
    assert not (HERE/'result.json').exists() and not (HERE/'certificate.json').exists()
    assert failure['inputs_sha256_start']==closed['inputs_sha256_start']==closed['inputs_sha256_end']
    deps=[]
    for name,expected in closed['inputs_sha256_end'].items():
        p=ROOT/name;assert pin(p)==expected
        if p.parent!=HERE:deps.append(row(p))
    runtime=closed['external_runtime_identity'];rp=Path(runtime['path'])
    assert pin(rp)==runtime['sha256_start']==runtime['sha256_end'] and rp.stat().st_size==runtime['bytes']
    files=[row(p) for p in sorted(HERE.iterdir()) if p.is_file() and p.name!='files.json']
    assert sum(r['bytes'] for r in files)<20000000
    manifest={'schema':'fixed-F-failed-production-and-raw-return-package-v1','files':files,
        'total_bytes':sum(r['bytes'] for r in files),'read_only_dependencies':sorted(deps,key=lambda x:x['path']),
        'external_read_only_runtime_identity':runtime,
        'primary_calls':1,'conditional_auxiliary_calls':0,'child_launches':1,'child_exit_code':1,
        'production_outcome':'rejected_returned_primal_inconclusive',
        'production_stage':'validate_primary_primal_dual','raw_primal_violated_rows':38,
        'original_prepared_sources_unchanged':True,'all_model_inputs_hashes_start_equal_end':True,
        'raw_primal_and_dual_retained':True,'certificate_produced_by_this_producer':False,
        'certificate_verifier_invocations':0,'certificate_verifier_not_applicable':closed['certificate_verifier_not_applicable'],
        'no_solver_retry_or_automatic_sign_changes':True,
        'independent_raw_dual_certificate_may_be_valid':True,
        'independent_source_and_rawdual_review_in_separate_package':True,
        'scope':'One failed primal+dual production guard; not a mathematical refutation. A separately verified dual may prove Lower without claiming optimum. No other pairs are handled.',
        'new_global_joint_floor_proven':False,'new_unconditional_zero_proportion_proven':False,
        'new_kernel_queries':0,'Lean_runs':0,'complete_source_and_runtime_budget':'unknown',
        'website_submission_ready':False,'mutable_governance_dependency':False}
    with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(manifest,f,indent=2);f.write('\n')
    print(json.dumps({'path':out.relative_to(ROOT).as_posix(),'sha256':pin(out),
        'files':len(files),'total_bytes':manifest['total_bytes']}))

if __name__=='__main__':main()
