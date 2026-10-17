"""Freeze the sole failed fixed transfer budget and independent replay.

The original exact-ray package is immutable. This failed sufficient
budget removes no old analytic obligation and permits no alternate trial.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,sys
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
AUDIT=ROOT/'research-goal-20261017-transfer-budget-audit';OUT=HERE/'transfer-budget-files.json'
def rec(p,name=None):return {'path':name or p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
assert not OUT.exists() and (AUDIT/'audit-files.json').exists()
data=json.loads((HERE/'transfer-budget.json').read_bytes());receipt=json.loads((HERE/'budget-receipt.json').read_bytes());monitor=json.loads((HERE/'budget-monitor.json').read_bytes())
assert receipt['phase']=='fixed_transfer_budget_FAILED_cost_not_below_margin' and not data['strict_K_less_than_margin']
assert F(data['total_cost_K'])>=F(data['fixed_full_certificate_margin'])>0
assert monitor['worker_exit_code']==0 and monitor['termination_reason'] is None and monitor['worker_processes_launched']==1
assert data['optimizer_calls']==data['eigh_calls']==data['rank_precision_parameter_trials']==data['Lean_invocations']==0
files=[p for p in HERE.iterdir() if p.is_file() and p!=OUT]+[p for p in AUDIT.iterdir() if p.is_file()]
assert all(not p.name.endswith('.partial') and p.stat().st_size<40*1024**2 for p in files)
names={p.relative_to(ROOT).as_posix() for p in files};deps={}
docs=[data,receipt,monitor]+[json.loads(p.read_bytes()) for p in AUDIT.iterdir() if p.suffix=='.json']
def bind(name,h,bytecount=None):
    p=ROOT/name;actual=rec(p,name);assert actual['sha256']==h
    if bytecount is not None:assert actual['bytes']==bytecount
    assert not name.startswith('tmp/')
    if name not in names:deps[name]=actual
for doc in docs:
    for label in ['source_sha256','input_sha256']:
        if label+'_start' in doc:
            assert doc[label+'_start']==doc[label+'_end']
            for name,h in doc[label+'_start'].items():bind(name,h)
        elif isinstance(doc.get(label),dict):
            for name,h in doc[label].items():bind(name,h)
    for label in ['files','package_files','dependency_files']:
        for r in doc.get(label,[]):bind(r['path'],r['sha256'],r.get('bytes'))
assert not names&set(deps)
out={'scope':__doc__,'package_files':[rec(p) for p in sorted(files,key=lambda p:p.relative_to(ROOT).as_posix())],
    'dependency_files':[deps[k] for k in sorted(deps)],'independent_exact_replay_passed':True,
    'original_full_ray_pin_sha256':'c19797f38f2a7687817735b91163bf329d6f2ad7cb26e9989b3e76bb99f5ceae',
    'single_fixed_budget_evaluation':True,'same_original_lambda_Gram_and_certificate':True,'same_case_and_target':True,
    'no_alternate_box_or_SOS_bound_tried':True,'exact_K_greater_or_equal_margin':True,
    'display_only_cost_scalar180':receipt['cost180_scalar_float_hint'],'display_only_cost_gradientGram18':receipt['cost18_Gram_float_hint'],
    'display_only_cost_sublevelGram1':receipt['cost_sublevel_float_hint'],'display_only_total_K':receipt['total_K_float_hint'],
    'display_only_original_margin':receipt['margin_float_hint'],'old_analytic_dependencies_removed':False,
    'peak_working_set_bytes':monitor['observed_peak_working_set_bytes'],'memory_guard_triggered':False,
    'optimizer_calls':0,'eigh_calls':0,'Lean_invocations':0,'rank_precision_parameter_trials':0,
    'actual_cell_exclusion_Lean_proved':False,'new_unconditional_zero_proportion_proven':False,'website_submission_ready':False}
OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
print(json.dumps({'manifest_sha256':rec(OUT)['sha256'],'package_files':len(files),'dependencies':len(deps),
    'package_bytes':sum(p.stat().st_size for p in files),'largest_package_file':max(p.stat().st_size for p in files)}))
