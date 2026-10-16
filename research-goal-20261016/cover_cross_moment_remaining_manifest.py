"""Pin the stopped six-case batch, standalone replay and parent-union audit."""
from pathlib import Path
import gzip,hashlib,json
HERE=Path(__file__).parent;ROOT=HERE.parent;sha=lambda b:hashlib.sha256(b).hexdigest()
FILES=['cover_cross_moment_remaining_probe.py','cover_cross_moment_remaining_archive.py',
  'cover_cross_moment_remaining_replay.py','cover_cross_moment_remaining_note.md',
  'cover_cross_moment_remaining_manifest.py','cover-cross-moment-overlap.json',
  'cover-cross-moment-remaining-evidence/proof.json.gz',
  'cover-cross-moment-remaining-evidence/manifest.json',
  'cover-cross-moment-remaining-evidence/independent-replay.json']


def row(path):
    p=ROOT/path;b=p.read_bytes();return {'path':path,'bytes':len(b),'sha256':sha(b)}


def main():
    folder=HERE/'cover-cross-moment-remaining-evidence';packed=(folder/'proof.json.gz').read_bytes();doc=json.loads(gzip.decompress(packed))
    replay=json.loads((folder/'independent-replay.json').read_bytes());assert replay['all_supply_and_ancestor_checks_passed']
    assert replay['archive_sha256']==sha(packed) and replay['full_batch_recovered_byte_identical']
    assert replay['script_sha256']==sha((HERE/'cover_cross_moment_remaining_replay.py').read_bytes())
    overlap=json.loads((HERE/'cover-cross-moment-overlap.json').read_bytes());assert overlap['new_distinct_regions']==1 and overlap['union_non_nested_regions']==15
    files=[row('research-goal-20261016/'+name) for name in FILES];own={r['path'] for r in files}
    dependencies={name:digest for name,digest in replay['dependency_sources_sha256'].items() if name not in own}
    dependencies.update(doc['source']['input_sha256'])
    for name,digest in dependencies.items():assert sha((ROOT/name).read_bytes())==digest,name
    data=['research-goal-20261016/cover_newjet.json','research-20261016-followup/window_reweight_rational.json']
    result={'scope':'Stopped fixed six-parent single-midpoint energy/RLT extension, zero new strict exclusions; complete standalone finite-supply/ancestor replay and separate local positive-union audit.',
      'files':files,'file_count':len(files),'total_bytes':sum(r['bytes'] for r in files),
      'external_source_dependencies_sha256':dependencies,'external_data_dependencies':[row(p) for p in data],
      'discovery_only_inputs':[row('research-goal-20261016/'+n) for n in ['cover-curvature-parent64.input.json.gz','cover-lifted-graph-energy8.json']],
      'positive_union_source_digests':overlap['sources_sha256'],'six_case_new_strict_exclusions':0,
      'prior_local_positive_regions':14,'updated_local_positive_regions':15,'new_distinct_positive_regions_from_first_two':1,
      'all_six_supply_and_ancestor_checks_passed':True,'exact_LP_primal_feasibility_verified':False,
      'actual_Lean_exclusions_in_six_batch':0,'complete_global_cover':False,'new_zero_proportion_proven':False,'submission_ready':False}
    out=HERE/'cover-cross-moment-remaining-files.json';out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'manifest':out.relative_to(ROOT).as_posix(),'sha256':sha(out.read_bytes()),'files':len(files),'bytes':result['total_bytes']}),flush=True)
if __name__=='__main__':main()
