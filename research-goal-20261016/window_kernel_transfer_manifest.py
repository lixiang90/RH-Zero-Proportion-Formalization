"""Pin the bounded scalar-transfer design and its two unsuccessful LP pilots."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def item(path):
    return {'path':str(path.relative_to(ROOT)).replace('\\','/'),
            'bytes':path.stat().st_size,'sha256':sha(path)}


def main():
    names=['window_kernel_floor_transfer_design.py','window-kernel-floor-transfer-design.json',
           'window_kernel_floor_transfer_note.txt','window_kernel_scaled_transfer_pilot.py',
           'window-kernel-scaled-transfer-pilot.json','window_kernel_compact_transfer_pilot.py',
           'window-kernel-compact-transfer-pilot.json','window_kernel_scaled_transfer_note.txt',
           Path(__file__).name]
    design=json.loads((HERE/names[1]).read_bytes())
    unbounded=json.loads((HERE/names[4]).read_bytes())
    compact=json.loads((HERE/names[6]).read_bytes())
    dependencies={}
    for path,digest in design['source_sha256'].items():
        assert sha(ROOT/path)==digest
        if path not in {str((HERE/n).relative_to(ROOT)).replace('\\','/') for n in names}:
            dependencies[path]=digest
    for doc in [unbounded,compact]:
        assert doc['source_sha256_start']==doc['source_sha256_end'] and doc['all_sources_unchanged']
        assert doc['maximum_LP_calls']==1 and doc['LP_time_limit_seconds']==45
        assert doc['LP']['success'] and doc['LP']['status']==0
        assert doc['LP']['lambda_by_deleted_vertex_hint']==[0.]*10
        for path,digest in doc['source_sha256_start'].items():
            assert sha(ROOT/path)==digest
            if path not in {str((HERE/n).relative_to(ROOT)).replace('\\','/') for n in names}:
                dependencies[path]=digest
    assert compact['LP']['shared_rho_hint']==0.
    assert not compact['LP']['exceeds_goal_floor_hint']
    energy=ROOT/'StructuralGoal20261016/WindowEnergyBound.lean'
    dependencies[str(energy.relative_to(ROOT)).replace('\\','/')]=sha(energy)
    sealed=HERE/'cover-residual-psd-rational-files.json'
    assert sha(sealed)=='5995d2ba510e40e31edbd17d3337a4f39c89acc62e209c016b0d584464714c6b'
    dependencies[str(sealed.relative_to(ROOT)).replace('\\','/')]=sha(sealed)
    site=F(json.loads((ROOT/'research-20261016-w10-cert/current-record-review.json').read_bytes())['current_record_exact'])
    h=F(1680240849522559118481,2500000000000000000000)
    b=F(11055671,2500000000)
    assert F(compact['goal_floor'])==1-(h-b)/(site+F(1,100000))
    out={'scope':__doc__,'package_files':[item(HERE/n) for n in names],
         'dependencies':[item(ROOT/p) for p in sorted(dependencies)],
         'unscaled_design_status':'Exact interval/algebra audit with stated analytic inputs; no Lean invocation.',
         'scaled_pilots_status':'Two separate one-shot floating discovery LPs, one fixed scale, neither useful; no exact uniform comparison certificate.',
         'formal_H':str(h),'new_pressure':str(b),
         'formal_goal_floor':compact['goal_floor'],
         'prior_exact_relaxation_package_unchanged':True,
         'new_unconditional_zeta_bound_proven':False}
    target=HERE/'window-kernel-transfer-files.json'
    target.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'package_files':len(names),'dependencies':len(dependencies),
                      'manifest_sha256':sha(target),'all_input_hashes_match':True}))


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
