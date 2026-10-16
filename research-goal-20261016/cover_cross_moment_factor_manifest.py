"""Freeze the two grouped proof variants and an actual-consumer JSON view."""
from pathlib import Path
import copy,gzip,hashlib,json
import cover_cross_moment_factor_replay as replay
HERE=Path(__file__).parent;ROOT=HERE.parent;sha=lambda b:hashlib.sha256(b).hexdigest()


def row(path):
    p=ROOT/path;b=p.read_bytes();return {'path':path,'bytes':len(b),'sha256':sha(b)}


def main():
    folder=HERE/'cover-cross-moment-factor-friendly-evidence';packed=(folder/'proof.json.gz').read_bytes();doc=json.loads(gzip.decompress(packed))
    params=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    checker=replay.support.graph.GraphReplay(json.loads((HERE/'cover_newjet.json').read_bytes()));states={r['path']:r['before'] for r in doc['source']['cases']};cases=[]
    for r in doc['records']:
        state=states[r['path']];bounds,mid,rad=replay.boxes(state,params,checker);case=copy.deepcopy(r)
        case.update({'cell':state,'physical_gap_center':list(map(str,mid)),'physical_gap_radius':list(map(str,rad)),
          'tight_derivative_bounds':[[str(l),str(u)] for l,u in bounds[9:50]]});cases.append(case)
    view={'schema':'affine-factor-friendly-consumer-view-v1','coordinate_scale':32768,'parameter_denominator':10**10,
      'old_row_denominator':str(2*32768*10**15*10**10),'integerization_denominator':str(10**30),
      'variable_layout':{'g':[0,9],'u':[9,50],'h_upper_triangle':[50,95],'q_row_major_9x41':[95,464]},
      'proof_gzip_sha256':sha(packed),'provenance':doc['provenance'],'cases':cases,
      'actual_Lean_exclusions':0,'complete_global_cover':False,'new_zero_proportion_proven':False}
    p=HERE/'cover-cross-moment-factor-friendly-cases.json';p.write_text(json.dumps(view,separators=(',',':'))+'\n',encoding='utf8')
    names=['cover_cross_moment_factor_compress.py','cover_cross_moment_factor_replay.py','cover_cross_moment_factor_friendly.py',
      'cover_cross_moment_factor_note.md','cover_cross_moment_factor_manifest.py','cover-cross-moment-factor-friendly-cases.json']
    dependencies={};summaries=[]
    for stem in ['cover-cross-moment-factor-evidence','cover-cross-moment-factor-friendly-evidence']:
        for name in ['proof.json.gz','comparison.json.gz','manifest.json','independent-replay.json']:names.append(stem+'/'+name)
        receipt=json.loads((HERE/stem/'independent-replay.json').read_bytes());m=json.loads((HERE/stem/'manifest.json').read_bytes())
        assert receipt['all_checks_passed'] and receipt['strict_local_integer_systems']==2
        assert receipt['script_sha256']==sha((HERE/'cover_cross_moment_factor_replay.py').read_bytes())
        assert receipt['proof_gzip_sha256']==m['proof_gzip_sha256'] and receipt['comparison_gzip_sha256']==m['comparison_gzip_sha256']
        dependencies.update(receipt['dependency_sources_sha256']);summaries.append({'variant':stem,'proof_gzip_bytes':m['proof_gzip_bytes'],'proof_gzip_sha256':m['proof_gzip_sha256'],'strict_systems':2})
    files=[row('research-goal-20261016/'+name) for name in names];own={r['path'] for r in files};dependencies={p:h for p,h in dependencies.items() if p not in own}
    for path,digest in dependencies.items():assert sha((ROOT/path).read_bytes())==digest,path
    data=['research-goal-20261016/cover_newjet.json','research-20261016-followup/window_reweight_rational.json',
      'research-goal-20261016/window-moment-friendly-packets.json','research-goal-20261016/cover-curvature-actual-active.json']
    result={'scope':'Exact affine-factor compression of the same frozen strict two moment certificates; original and Friendly energy0 variants, independent arithmetic replay, no new exclusions.',
      'files':files,'file_count':len(files),'total_bytes':sum(r['bytes'] for r in files),
      'external_source_dependencies_sha256':dependencies,'external_data_dependencies':[row(p) for p in data],
      'variants':summaries,'factor_groups_per_case':[103,106],'all_464_unrounded_coefficients_and_constants_equal':True,
      'original_energy_weights_preserved':True,'independent_finite_replay_passed':True,'new_cell_exclusions':0,
      'actual_Lean_exclusions_instantiated_here':0,'complete_global_cover':False,'new_zero_proportion_proven':False,'submission_ready':False}
    out=HERE/'cover-cross-moment-factor-files.json';out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'manifest':out.relative_to(ROOT).as_posix(),'sha256':sha(out.read_bytes()),'files':len(files),'bytes':result['total_bytes'],
      'friendly_view_bytes':p.stat().st_size,'friendly_view_sha256':sha(p.read_bytes())}),flush=True)
if __name__=='__main__':main()
