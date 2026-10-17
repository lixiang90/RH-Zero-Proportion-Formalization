"""Freeze the independently replayed fixed-ray outer-model contradiction.

Mutable governance documents are historical provenance, verified against
archived snapshots instead of freezing the live main-round counter.
Mathematical inputs, producer sources and audit sources are hash-bound.
"""
from pathlib import Path
import gzip,hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
AUDIT=ROOT/'research-goal-20261017-exact-ray-audit';OUT=HERE/'exact-ray-files.json'
def rec(p,name=None):return {'path':name or p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
assert not OUT.exists()
cert=json.loads((HERE/'exact-enclosure-certificate.json').read_bytes());quant=json.loads((HERE/'quantization.json').read_bytes())
combo=json.loads((HERE/'exact-combination.json').read_bytes());monitor=json.loads((HERE/'exact-monitor.json').read_bytes())
ray=json.loads(gzip.decompress((HERE/'quantized-ray.json.gz').read_bytes()))
assert cert['strict_negative_constant_upper'] and cert['constant_upper_numerator']==-999999997576201063457841009740
assert combo['phase']=='exact_interval_and_box_certificate_PASS' and monitor['worker_exit_code']==0 and monitor['termination_reason'] is None
assert quant['eigh_calls']==73 and combo['eigh_calls']==0 and combo['optimizer_calls']==0
assert (AUDIT/'audit-files.json').exists()
history=json.loads((HERE/'governance-provenance.json').read_bytes())['snapshots'];historical={r['historical_path']:r for r in history}
for r in history:
    actual=rec(ROOT/r['snapshot_path']);assert actual['sha256']==r['historical_sha256']==r['snapshot_sha256'] and not r['mathematical_premise']
files=[p for p in HERE.iterdir() if p.is_file() and p!=OUT]+[p for p in AUDIT.iterdir() if p.is_file()]
assert all(not p.name.endswith('.partial') and p.stat().st_size<40*1024**2 for p in files)
names={p.relative_to(ROOT).as_posix() for p in files};deps={};runtime={};reconstructed={}
def bind(name,h,bytecount=None):
    if name in historical:
        assert h==historical[name]['historical_sha256'];return
    p=Path(name) if Path(name).is_absolute() else ROOT/name;actual=rec(p,name);assert actual['sha256']==h
    if bytecount is not None:assert actual['bytes']==bytecount
    if name.startswith('tmp/') or not p.is_relative_to(ROOT):runtime[name]=actual
    elif name not in names:deps[name]=actual
docs=[quant,combo,monitor,ray,cert]
docs += [json.loads(p.read_bytes()) for p in AUDIT.iterdir() if p.suffix=='.json']
for doc in docs:
    for label in ['input_sha256','source_sha256']:
        if label+'_start' in doc:
            assert doc[label+'_start']==doc[label+'_end']
            for name,h in doc[label+'_start'].items():bind(name,h)
        elif isinstance(doc.get(label),dict):
            for name,h in doc[label].items():bind(name,h)
    for label in ['files','package_files','dependency_files']:
        for r in doc.get(label,[]):bind(r['path'],r['sha256'],r.get('bytes'))
# This already-published input is restored from its existing verified
# pieces; its cache must not be uploaded again by this new manifest.
name='research-goal-20261017-swap-family-quartic/swap-family-normalized.json.gz'
if name in deps:
    reconstructed[name]=deps.pop(name)
    for extra in ['restore_inputs.py','restore-inputs.json']:
        p=ROOT/'research-goal-20261017-swap-family-quartic'/extra;deps[p.relative_to(ROOT).as_posix()]=rec(p)
assert not (names&set(deps) or names&set(runtime) or names&set(reconstructed) or set(deps)&set(runtime) or set(deps)&set(reconstructed))
sizes=json.loads((HERE/'literal-size-estimate.json').read_bytes())
out={'scope':__doc__,'package_files':[rec(p) for p in sorted(files,key=lambda p:p.relative_to(ROOT).as_posix())],
    'dependency_files':[deps[k] for k in sorted(deps)],'reconstructed_dependency_files':[reconstructed[k] for k in sorted(reconstructed)],
    'runtime_dependency_files':[runtime[k] for k in sorted(runtime)],'historical_governance_provenance':history,
    'mutable_governance_is_not_a_mathematical_dependency':True,'independent_full_stdlib_replay_passed':True,
    'strict_upper_numerator':cert['constant_upper_numerator'],'strict_upper_denominator':cert['fixed_interval_denominator'],
    'strict_margin':cert['strict_margin'],'enclosed_atoms':cert['enclosed_nonzero_atoms'],'literal_exact_cancellation_claimed':False,
    'nonnegative_scalar_weights':14562,'exact_zero_unbounded_slack_rows':[5793,5794],'integer_Gram_blocks':73,
    'eigh_calls_in_fixed_quantization':73,'eigh_calls_after_quantization':0,'new_optimizer_calls':0,
    'same_case_and_target':True,'outer_polynomial_model_infeasible':True,'actual_cell_exclusion_Lean_proved':False,
    'active_old_analytic_dependencies_removed':False,'all181_actual_sextic_rows_active':True,
    'literal_size_estimate':sizes,'website_2MB_source_contract_met':False,'Lean_invocations':0,
    'complete_coverage_proven':False,'new_unconditional_zero_proportion_proven':False,'website_submission_ready':False}
OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
print(json.dumps({'manifest_sha256':rec(OUT)['sha256'],'package_files':len(files),'dependencies':len(deps),'reconstructed_only':len(reconstructed),
    'runtime_only':len(runtime),'package_bytes':sum(p.stat().st_size for p in files),'largest_package_file':max(p.stat().st_size for p in files)}))
