"""Freeze all eight-swap static rows, one solve, and exact feasibility replay."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
AUDIT=ROOT/'research-goal-20261017-swap-family-audit'
OUT=HERE/'swap-family-files.json'
def record(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def main():
    assert not OUT.exists()
    files=[p for p in HERE.iterdir() if p.is_file() and p!=OUT]+[p for p in AUDIT.iterdir() if p.is_file()]
    names={p.relative_to(ROOT).as_posix() for p in files};deps={}
    reports=[HERE/'swap-family-quartic-build.json',HERE/'swap-family-normalized-build.json',HERE/'swap-family-cone.json',
        HERE/'swap-family-exact-primal.json',HERE/'swap-family-result-replay.json',AUDIT/'independent-replay.json']
    for p in reports:
        q=json.loads(p.read_bytes());a=q.get('source_sha256_start',q.get('input_sha256_start'));b=q.get('source_sha256_end',q.get('input_sha256_end'));assert a==b
        for name,h in a.items():
            item=record(ROOT/name);assert item['sha256']==h
            if name not in names:deps[name]=item
    for p in [AUDIT/'audit-files.json',ROOT/'research-goal-20261017-swap67-audit/audit-files.json']:
        q=json.loads(p.read_bytes())
        for item in q.get('files',q.get('package_files',[]))+q.get('dependency_files',[]):
            r=record(ROOT/item['path']);assert r['sha256']==item['sha256']
            if item['path'] not in names:deps[item['path']]=r
        if p.relative_to(ROOT).as_posix() not in names:deps[p.relative_to(ROOT).as_posix()]=record(p)
    cone=json.loads((HERE/'swap-family-cone.json').read_bytes());proof=json.loads((HERE/'swap-family-exact-primal.json').read_bytes());replay=json.loads((HERE/'swap-family-result-replay.json').read_bytes())
    assert cone['phase']=='completed_single_shared_quartic_eight_swap_SCS' and not cone['any_positive_hint']
    assert proof['exact_eight_swap_quartic_outer_relaxation_feasible'] and proof['negative_linear_rows']==0
    assert replay['passed'] and replay['rational_linear_rows_checked']==5803 and replay['strict_positive_PSD_blocks_checked']==47
    transport=json.loads((HERE/'restore-inputs.json').read_bytes())
    for row in transport['outputs']:
        raw=b''.join((HERE/part['name']).read_bytes() for part in row['parts'])
        assert len(raw)==row['bytes'] and hashlib.sha256(raw).hexdigest()==row['sha256']==record(HERE/row['name'])['sha256']
        assert all(part['bytes']<=3*1024*1024 for part in row['parts'])
    out={'scope':__doc__,'package_files':[record(p) for p in sorted(files,key=lambda p:p.relative_to(ROOT).as_posix())],
        'dependency_files':[deps[k] for k in sorted(deps)],'single_case':'r001000001000100110011001',
        'complete_fixed_adjacent_swap_family':8,'additional_unsoftened_rows':8,'scalar_rows':5803,'unchanged_PSD_blocks':47,
        'one_actual_SCS_call':True,'solver_settings_unchanged':True,'unadjusted_rational_moments':714,'energy_slack':'0',
        'exact_outer_relaxation_feasibility_independently_replayed':True,'strict_PD_blocks':47,
        'large_originals_restorable_from_lossless_3MiB_parts':True,'transport_manifest':'restore-inputs.json',
        'new_actual_analytic_instances_Lean_proved':False,'actual_F_or_KKT_counterexample':False,
        'cell_exclusion_proven':False,'new_zero_proportion_proven':False}
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'manifest_sha256':record(OUT)['sha256'],'files':len(files),'dependencies':len(deps),'package_bytes':sum(p.stat().st_size for p in files)}))
if __name__=='__main__':main()
