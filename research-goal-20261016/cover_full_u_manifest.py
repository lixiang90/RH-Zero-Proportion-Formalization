"""Freeze the first full-U model, independent audit, and unsuccessful full51 solve."""
from pathlib import Path
import hashlib,json

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def item(p):return {'path':str(p.relative_to(ROOT)).replace('\\','/'),'bytes':p.stat().st_size,'sha256':sha(p)}
def read(p):
    def bad(s):raise ValueError('nonfinite token '+s)
    return json.loads(p.read_text(encoding='utf8'),parse_constant=bad)


def main():
    names=['cover_full_u_model.py','cover-full-u-model.json','cover_full_u_replay.py','cover-full-u-replay.json',
           'cover_full_u_joint_cone.py','cover-full-u-joint-cone.json','cover_full_u_note.txt',Path(__file__).name]
    package={str((HERE/n).relative_to(ROOT)).replace('\\','/') for n in names};dependencies={}
    model=read(HERE/names[1]);replay=read(HERE/names[3]);scs=read(HERE/names[5])
    assert model['variables']==1325 and len(model['new_linear_rows'])==4264
    assert replay['status']=='full_U_polynomial_model_and_strict_toy_independently_verified'
    assert scs['phase']=='completed_single_full_U_SCS' and scs['solver_calls_authorized']==1
    assert scs['solver_info']['iter']==10000 and not scs['positive_energy_slack_hint']
    assert 'inaccurate' in scs['solver_info']['status'] and scs['strict_certificate'] is None
    for doc,prefix in [(model,'source_sha256'),(replay,'source_sha256'),(scs,'input_sha256')]:
        assert doc[prefix+'_start']==doc[prefix+'_end'] and doc['all_sources_unchanged']
        for p,h in doc[prefix+'_start'].items():
            assert sha(ROOT/p)==h
            if p not in package:dependencies[p]=h
    prior=HERE/'cover-dynamic-sector-files.json'
    assert sha(prior)=='7ae3208f705a7fec9ca0796ff47f7c23426356c7b140e6920933be8048e28922'
    out={'scope':__doc__,'package_files':[item(HERE/n) for n in names],
         'dependencies':[item(ROOT/p) for p in sorted(dependencies)],
         'mathematical_increment':'Full derivative cross moment box-RLT; strict independent-cone nonimplication toy margin 14/25.',
         'first_numerical_result':'One full51 SCS reaches max_iters with material violations; neither feasibility nor exclusion proved.',
         'prior_dynamic_sector_package_unchanged':True,'new_zero_proportion_proven':False}
    path=HERE/'cover-full-u-files.json';path.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'package_files':len(names),'dependencies':len(dependencies),'manifest_sha256':sha(path),'all_hashes_match':True}))


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
