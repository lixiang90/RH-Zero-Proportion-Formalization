"""Freeze the sole deterministic Gram-tail representation measurement.

The cell was already covered historically and is unrelated to the current
frontier. The retained arithmetic certificate passes, its ordinary data
source fails the2MB gate, and no further simplification is authorized.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,sys
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;AUDIT=ROOT/'research-goal-20261017-fixed-gram-tail-audit'
OUT=HERE/'fixed-tail-files.json'
def rec(p,name=None):return {'path':name or p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
assert not OUT.exists() and (AUDIT/'audit-files.json').exists()
prune=json.loads((HERE/'pruning.json').read_bytes());selection=json.loads((HERE/'tail-selection.json').read_bytes())
cert=json.loads((HERE/'retained-enclosure-certificate.json').read_bytes());receipt=json.loads((HERE/'retained-combination.json').read_bytes());monitor=json.loads((HERE/'retained-monitor.json').read_bytes())
assert cert['strict_negative_constant_upper'] and receipt['phase']=='exact_interval_and_box_certificate_PASS'
assert monitor['worker_exit_code']==0 and monitor['termination_reason'] is None and monitor['worker_processes_launched']==1
assert prune['new_eigh_calls']==prune['optimizer_calls']==prune['integer_rerounding_operations']==0
assert selection['deleted_columns']==125 and selection['retained_columns']==2885
assert F(selection['total_deleted_cost'])<=F(selection['single_tail_budget'])
assert F(cert['strict_margin'])>=F(selection['predicted_retained_margin_at_least'])>0
files=[p for p in HERE.iterdir() if p.is_file() and p!=OUT]+[p for p in AUDIT.iterdir() if p.is_file()]
assert all(not p.name.endswith('.partial') and p.stat().st_size<40*1024**2 for p in files)
names={p.relative_to(ROOT).as_posix() for p in files};deps={};reconstructed={}
def bind(name,h,bytecount=None):
    p=ROOT/name;actual=rec(p,name);assert actual['sha256']==h
    if bytecount is not None:assert actual['bytes']==bytecount
    assert not name.startswith('tmp/')
    if name not in names:deps[name]=actual
docs=[prune,selection,cert,receipt,monitor]+[json.loads(p.read_bytes()) for p in AUDIT.iterdir() if p.suffix=='.json']
for doc in docs:
    for label in ['source_sha256','input_sha256']:
        if label+'_start' in doc:
            assert doc[label+'_start']==doc[label+'_end']
            for name,h in doc[label+'_start'].items():bind(name,h)
        elif isinstance(doc.get(label),dict):
            for name,h in doc[label].items():bind(name,h)
    for label in ['files','package_files','dependency_files']:
        for r in doc.get(label,[]):bind(r['path'],r['sha256'],r.get('bytes'))
scopepaths=['research-goal-20261017-global-relevance-audit/global-relevance.json','research-goal-20261017-global-relevance-audit/audit_relevance.py']
assert rec(ROOT/scopepaths[0])['sha256']=='0053de28579a0bd8646df4dedb14d10735e5324756f415b58f523bc08377ad85'
for name in scopepaths:deps[name]=rec(ROOT/name)
name='research-goal-20261017-swap-family-quartic/swap-family-normalized.json.gz'
if name in deps:
    reconstructed[name]=deps.pop(name)
    for extra in ['restore_inputs.py','restore-inputs.json']:
        p=ROOT/'research-goal-20261017-swap-family-quartic'/extra;deps[p.relative_to(ROOT).as_posix()]=rec(p)
assert not names&set(deps) and not names&set(reconstructed) and not set(deps)&set(reconstructed)
out={'scope':__doc__,'package_files':[rec(p) for p in sorted(files,key=lambda p:p.relative_to(ROOT).as_posix())],
    'dependency_files':[deps[k] for k in sorted(deps)],'reconstructed_dependency_files':[reconstructed[k] for k in sorted(reconstructed)],
    'scope_provenance_paths_not_mathematical_premises':scopepaths,'independent_exact_replay_passed':True,
    'original_full_certificate_unchanged_sha256':'c19797f38f2a7687817735b91163bf329d6f2ad7cb26e9989b3e76bb99f5ceae',
    'deleted_columns':125,'retained_columns':2885,'retained_integer_entries':182495,
    'strict_upper_numerator':cert['constant_upper_numerator'],'strict_upper_denominator':10**30,'strict_margin':cert['strict_margin'],
    'source_size':selection['source_size'],'ordinary_data_only_source_fails_2MB_gate':True,
    'historical_case_already_accepted':True,'current_frontier_excluded_by_this_packet':False,
    'new_optimizer_calls':0,'new_eigh_calls':0,'new_integer_rerounding':0,'Lean_invocations':0,'alternate_simplification_trials':0,
    'actual_cell_exclusion_Lean_proved':False,'complete_global_cover_proven':False,'new_unconditional_zero_proportion_proven':False,
    'website_source_contract_met':False,'website_submission_ready':False,'further_computation_stopped':True}
OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
print(json.dumps({'manifest_sha256':rec(OUT)['sha256'],'package_files':len(files),'dependencies':len(deps),'reconstructed_only':len(reconstructed),
    'package_bytes':sum(p.stat().st_size for p in files),'largest_package_file':max(p.stat().st_size for p in files)}))
