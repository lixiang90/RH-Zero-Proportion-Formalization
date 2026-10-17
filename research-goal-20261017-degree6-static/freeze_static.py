"""Freeze one resource-gated degree6 STATIC model and independent decoder."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
AUDIT=ROOT/'research-goal-20261017-degree6-audit';OUT=HERE/'degree6-files.json'
def rec(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
assert not OUT.exists();build=json.loads((HERE/'degree6-build.json').read_bytes());audit=json.loads((AUDIT/'independent-replay.json').read_bytes())
assert build['resource_gate_passed'] and build['phase']=='complete_static_degree6_cost_gate_passed'
assert audit['status']=='complete_factored_degree6_representation_independently_decoded' and audit['all_inputs_unchanged']
assert build['source_sha256_start']==build['source_sha256_end'] and audit['source_sha256_start']==audit['source_sha256_end']
assert audit['block_entries_checked']==96580 and audit['old_exact_principal_forms_preserved']==4070 and audit['old_scalar_rows_preserved_by_adapter']==5803
files=[p for p in HERE.iterdir() if p.is_file() and p!=OUT]+[p for p in AUDIT.iterdir() if p.is_file()]
names={p.relative_to(ROOT).as_posix() for p in files};deps={}
for pins in [build['source_sha256_start'],audit['source_sha256_start']]:
    for name,h in pins.items():
        r=rec(ROOT/name);assert r['sha256']==h
        if name not in names:deps[name]=r
for name in ['degree6-audit-files.json']:
    manifest=json.loads((AUDIT/name).read_bytes())
    for r in manifest.get('files',manifest.get('package_files',[])):
        assert rec(ROOT/r['path'])['sha256']==r['sha256']
peak=max(m['peak_working_set_bytes'] for m in build['memory_snapshots']);assert peak<1536*1024**2
assert build['model_uncompressed_bytes']<40*1024**2 and all(p.stat().st_size<40*1024**2 for p in files)
out={'scope':__doc__,'package_files':[rec(p) for p in sorted(files,key=lambda p:p.relative_to(ROOT).as_posix())],
    'dependency_files':[deps[k] for k in sorted(deps)],'same_case':'r001000001000100110011001','target':'11/1250',
    'optimization_variables_including_slack':5005,'slack_column':5004,'scalar_rows':14383,'PSD_blocks':73,'PSD_entries':96580,
    'independent_representation_decode_passed':True,'old_PSD_principal_entries_preserved':4070,'old_scalar_rows_preserved':5803,
    'new_moment_box_rows':8580,'peak_working_set_bytes':peak,'model_uncompressed_bytes':build['model_uncompressed_bytes'],
    'factored_mapping_complete':True,'resource_gate_passed':True,'new_points':0,'new_actual_analytic_inputs':0,
    'solver_calls':0,'Lean_invocations':0,'cloud_operations':0,'old_exact714_extension_decided':False,
    'strict_projection_shrink_proven':False,'cell_exclusion_proven':False,'new_zero_proportion_proven':False}
OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
print(json.dumps({'manifest_sha256':rec(OUT)['sha256'],'package_files':len(files),'dependencies':len(deps),'package_bytes':sum(p.stat().st_size for p in files)}))
