"""Pin one exact relaxation-feasibility obstruction and discovery provenance."""
from pathlib import Path
import hashlib,json
import cover_cross_moment_old_rows_replay as old

HERE=Path(__file__).parent;ROOT=HERE.parent
PACKAGE=['cover_residual_psd_rational_projection.py','cover-residual-psd-rational-projection.json',
    'cover_residual_psd_rational_inputs.py','cover-residual-psd-rational-inputs.json',
    'cover_residual_psd_rational_replay.py','cover-residual-psd-rational-replay.json',
    'cover_residual_psd_rational_obstruction.txt','cover_residual_psd_rational_manifest.py']
DISCOVERY=['cover_residual_psd_full_cone.py','cover-residual-psd-full-cone.json',
    'cover_residual_psd_bregman_full_cone.py','cover-residual-psd-bregman-full-cone.json']

def entry(path):
    raw=path.read_bytes();return {'path':path.relative_to(ROOT).as_posix(),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}

def main():
    receipt=json.loads((HERE/'cover-residual-psd-rational-replay.json').read_text())
    assert receipt['status']=='strict_exact_feasible_outer_relaxation_verified'
    assert receipt['rational_rows_checked']==43306 and receipt['finite_boxes_checked']==464 and receipt['strict_positive_LDL_blocks_checked']==41
    dependencies=old.dependency_hashes()
    for name in ['cover-residual-psd-rational-projection.json','cover-residual-psd-rational-inputs.json','cover-residual-psd-rational-replay.json']:
        data=json.loads((HERE/name).read_text())
        for path,value in data['input_sha256_start'].items():
            p=ROOT/path;assert hashlib.sha256(p.read_bytes()).hexdigest()==value;dependencies[path]=value
    for path,value in dependencies.items():assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==value
    sources=[]
    for name in DISCOVERY:
        p=HERE/name;r=entry(p);r['role']='discovery_only_not_mathematical_certificate'
        if p.suffix=='.json':r['nonstandard_NaN_token_count']=p.read_text().count('NaN')
        sources.append(r)
    result={'schema':'exact-residual-PSD-relaxation-obstruction-v1','scope':__doc__,
        'package_files':[entry(HERE/name) for name in PACKAGE],'SCS_discovery_sources_unchanged':sources,
        'dependency_sha256':dependencies,'path':receipt['path'],'rational_rows_checked':43306,'finite_boxes_checked':464,
        'exact_KKT_equalities':90,'strict_positive_rational_LDL_blocks':41,'block_size':11,
        'status':'strict_exact_feasible_point_of_named_outer_relaxation',
        'actual_Fw_counterexample':'not_claimed; nonzero position variances',
        'new_zero_proportion':'not_proven','global_cover':'not_proven','submission_ready':'no',
        'prior_26c0_package':'unchanged'}
    out=HERE/'cover-residual-psd-rational-files.json';assert not out.exists()
    out.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'package_files':len(PACKAGE),'discovery_files':len(DISCOVERY),
        'dependencies':len(dependencies),'manifest_sha256':hashlib.sha256(out.read_bytes()).hexdigest()}),flush=True)

if __name__=='__main__':main()
