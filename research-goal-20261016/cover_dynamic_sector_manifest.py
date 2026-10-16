"""Seal the dynamic secant-sector exact separation and one SCS discovery test."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def item(p):return {'path':str(p.relative_to(ROOT)).replace('\\','/'),'bytes':p.stat().st_size,'sha256':sha(p)}
def strict_json(p):
    def reject(s):raise ValueError('nonfinite JSON token '+s)
    return json.loads(p.read_text(encoding='utf8'),parse_constant=reject)


def main():
    names=['cover_dynamic_sector_static.py','cover-dynamic-sector-static.json',
           'cover_dynamic_sector_replay.py','cover-dynamic-sector-replay.json',
           'cover_dynamic_sector_full_cone.py','cover-dynamic-sector-full-cone.json',
           'cover_dynamic_sector_note.txt',Path(__file__).name]
    package={str((HERE/n).relative_to(ROOT)).replace('\\','/') for n in names}
    static=strict_json(HERE/names[1]);replay=strict_json(HERE/names[3]);scs=strict_json(HERE/names[5])
    assert static['exact_violated_cones']==7 and len(static['cones'])==41
    assert replay['strict_old_point_violations']==7 and replay['cones_checked']==41
    assert replay['status']=='all_41_dynamic_cones_and_7_exact_violations_independently_verified'
    assert scs['old_residual_blocks']==scs['new_dynamic_sector_blocks']==41
    assert scs['time_limit_seconds']==45 and scs['maximum_iterations']==10000
    assert scs['SCS_calls_authorized']==1 and scs['solver_info']['iter']<=10000
    assert scs['phase']=='completed_single_dynamic_sector_SCS' and not scs['positive_energy_slack_hint']
    assert scs['strict_certificate'] is None
    dependencies={}
    for doc,prefix in [(static,'source_sha256'),(replay,'source_sha256'),(scs,'input_sha256')]:
        assert doc[prefix+'_start']==doc[prefix+'_end'] and doc['all_sources_unchanged']
        for p,h in doc[prefix+'_start'].items():
            assert sha(ROOT/p)==h
            if p not in package:dependencies[p]=h
    prior=HERE/'cover-residual-psd-rational-files.json'
    assert sha(prior)=='5995d2ba510e40e31edbd17d3337a4f39c89acc62e209c016b0d584464714c6b'
    oldseal=strict_json(prior)
    # The previous seal already pins all imports used by the captured old model.
    for rows in oldseal.values():
        if not isinstance(rows,list):continue
        for row in rows:
            if isinstance(row,dict) and 'path' in row and 'sha256' in row:
                assert sha(ROOT/row['path'])==row['sha256']
                if row['path'] not in package:dependencies[row['path']]=row['sha256']
    for cone,norm in zip(static['cones'],scs['new_congruence_normalizations']):
        eps=F(cone['old_constant_error_normalization']);assert eps>0
        assert norm['congruence_diagonal']==['1']*10+[str(1/eps)]
        assert F(norm['cross_multiplier'])==1/eps and F(norm['bottom_multiplier'])==1/eps**2
    out={'scope':__doc__,'package_files':[item(HERE/n) for n in names],
         'dependencies':[item(ROOT/p) for p in sorted(dependencies)],
         'exact_result':'41 necessary dynamic cones; seven strictly separate a previously certified old-model point.',
         'numerical_result':'One 82-cone SCS solve gives no positive energy slack; no exact new-model feasibility or exclusion claim.',
         'prior_exact_relaxation_package_unchanged':True,
         'new_zero_proportion_proven':False}
    path=HERE/'cover-dynamic-sector-files.json'
    path.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'package_files':len(names),'dependencies':len(dependencies),
                      'manifest_sha256':sha(path),'all_hashes_match':True}))


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
