"""Pin exact KKT face equivalence, independent full replay and one reduced solve."""
from pathlib import Path
import hashlib,json

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def item(p):return {'path':str(p.relative_to(ROOT)).replace('\\','/'),'bytes':p.stat().st_size,'sha256':sha(p)}
def read(p):
    def bad(s):raise ValueError(s)
    return json.loads(p.read_text(encoding='utf8'),parse_constant=bad)


def main():
    names=['cover_full_u_face_model.py','cover-full-u-face-model.json.gz','cover-full-u-face-build.json',
        'cover_full_u_face_replay.py','cover-full-u-face-replay.json','cover_full_u_face_cone.py',
        'cover-full-u-face-cone.json','cover_full_u_face_note.txt',Path(__file__).name]
    package={str((HERE/n).relative_to(ROOT)).replace('\\','/') for n in names};dependencies={}
    build=read(HERE/names[2]);replay=read(HERE/names[4]);scs=read(HERE/names[6])
    assert build['status']=='exact_51_to_42_face_and_1325_to_902_map_verified'
    assert replay['status']=='exact_full_U_face_and_all_row_box_pullbacks_independently_verified'
    assert replay['original_rows_checked']==50221 and replay['distinct_rows']==46347
    assert scs['phase']=='completed_single_reduced42_SCS' and scs['solver_calls_authorized']==1
    assert scs['solver_info']['iter']==10000 and not scs['positive_energy_slack_hint']
    assert scs['strict_certificate'] is None and scs['mathematical_constraint_changes']==0
    assert sha(HERE/names[1])==build['compressed_model_sha256']
    for doc,prefix in [(build,'source_sha256'),(replay,'source_sha256'),(scs,'input_sha256')]:
        assert doc[prefix+'_start']==doc[prefix+'_end']
        for p,h in doc[prefix+'_start'].items():
            assert sha(ROOT/p)==h
            if p not in package:dependencies[p]=h
    prior=HERE/'cover-full-u-files.json'
    assert sha(prior)=='fef4caa3f4566b398d66a3d9e8b12e846e128fb5bf8188bca1e0284267db1e46'
    out={'scope':__doc__,'package_files':[item(HERE/n) for n in names],
        'dependencies':[item(ROOT/p) for p in sorted(dependencies)],
        'mathematical_model_changes':0,'exact_result':'51-to-42 PSD face and 1325-to-902 moment substitution; every original row and box retained.',
        'numerical_result':'One reduced SCS call reaches max_iters without an exclusion margin; no exact feasible point claimed.',
        'prior_full51_package_unchanged':True,'new_zero_proportion_proven':False}
    path=HERE/'cover-full-u-face-files.json';path.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'package_files':len(names),'dependencies':len(dependencies),'manifest_sha256':sha(path),'all_hashes_match':True}))


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
