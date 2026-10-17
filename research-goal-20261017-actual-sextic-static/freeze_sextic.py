"""Freeze one normalized-W absolute sextic STATIC packet and exact audit."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
AUDIT=ROOT/'research-goal-20261017-actual-sextic-audit';OUT=HERE/'actual-sextic-files.json'
def rec(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
assert not OUT.exists();build=json.loads((HERE/'sextic-build.json').read_bytes());audit=json.loads((AUDIT/'independent-replay.json').read_bytes());am=json.loads((AUDIT/'sextic-audit-files.json').read_bytes())
assert build['resource_gate_passed'] and build['phase']=='complete_coherent_actual_sextic_STATIC_packet_resource_gate_passed'
assert am['independent_exact_STATIC_replay_passed'] and audit['all_inputs_unchanged']
assert build['source_sha256_start']==build['source_sha256_end'] and audit['source_sha256_start']==audit['source_sha256_end']
assert build['new_scalar_rows']==181 and build['new_energy_row_unsoftened'] and build['old_model_retained']
assert not build['old_F0_used_by_new_energy'] and not build['old_wprime_used_by_new_envelopes']
files=[p for p in HERE.iterdir() if p.is_file() and p!=OUT]+[p for p in AUDIT.iterdir() if p.is_file()]
names={p.relative_to(ROOT).as_posix() for p in files};deps={}
for pins in [build['source_sha256_start'],audit['source_sha256_start']]:
    for name,h in pins.items():
        r=rec(ROOT/name);assert r['sha256']==h
        if name not in names:deps[name]=r
for r in am['files']+am.get('dependency_files',[]):
    item=rec(ROOT/r['path']);assert item['sha256']==r['sha256']
    if r['path'] not in names:deps[r['path']]=item
peak=max(m['peak_working_set_bytes'] for m in build['memory_snapshots']);assert peak<1536*1024**2
assert build['packet_uncompressed_bytes']<40*1024**2 and all(p.stat().st_size<4*1024**2 for p in files)
out={'scope':__doc__,'package_files':[rec(p) for p in sorted(files,key=lambda p:p.relative_to(ROOT).as_posix())],
    'dependency_files':[deps[k] for k in sorted(deps)],'single_case':'r001000001000100110011001','target':'11/1250',
    'original_positive_ledger_edges':41,'new_scalar_rows':181,'unsoftened_absolute_L6_energy':True,
    'new_energy_uses_old_F0':False,'new_envelopes_use_old_wprime_literals':False,'same_underlying_variables':9,
    'canonical_moments':5005,'new_PSD_blocks':0,'no_degree8_M1_localizers':True,
    'old14383rows_and73PSD_retained':True,'combined_scalar_rows':14564,'point_jet_orders':[0,1,2,3,4,5,6],
    'whole_w7_grid_cells':658,'independent_exact_STATIC_replay_passed':True,'peak_working_set_bytes':peak,
    'packet_uncompressed_bytes':build['packet_uncompressed_bytes'],'new_points_or_moment_evaluations':0,
    'solver_calls':0,'Lean_invocations':0,'new_actual_sampling_positions':0,'concrete_analytic_Lean_instances_proved':False,
    'strict_new_inequality_violation_proven':False,'cell_exclusion_proven':False,'new_zero_proportion_proven':False}
OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
print(json.dumps({'manifest_sha256':rec(OUT)['sha256'],'package_files':len(files),'dependencies':len(deps),'package_bytes':sum(p.stat().st_size for p in files)}))
