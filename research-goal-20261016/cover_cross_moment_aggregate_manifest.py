"""Pin optional single-round and exact-no-round aggregate supplements."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).parent;ROOT=HERE.parent;sha=lambda b:hashlib.sha256(b).hexdigest()
NAMES=['cover_cross_moment_single_round.py','cover_cross_moment_exact_aggregate.py',
  'cover-cross-moment-single-round.json','cover-cross-moment-single-round-replay.json',
  'cover-cross-moment-exact-aggregate.json','cover-cross-moment-exact-aggregate-replay.json',
  'cover_cross_moment_aggregate_note.md','cover_cross_moment_aggregate_manifest.py']


def item(path):
    p=ROOT/path;b=p.read_bytes();return {'path':path,'bytes':len(b),'sha256':sha(b)}


def main():
    single=json.loads((HERE/'cover-cross-moment-single-round-replay.json').read_bytes());integer=json.loads((HERE/'cover-cross-moment-exact-aggregate-replay.json').read_bytes())
    assert single['all_checks_passed'] and integer['all_checks_passed']
    assert single['script_sha256']==sha((HERE/'cover_cross_moment_single_round.py').read_bytes()) and integer['script_sha256']==sha((HERE/'cover_cross_moment_exact_aggregate.py').read_bytes())
    assert single['input_sha256']==sha((HERE/'cover-cross-moment-single-round.json').read_bytes())
    assert integer['input_sha256']==sha((HERE/'cover-cross-moment-exact-aggregate.json').read_bytes())
    files=[item('research-goal-20261016/'+n) for n in NAMES];own={f['path'] for f in files};deps={p:h for p,h in single['dependency_sources_sha256'].items() if p not in own}
    for p,h in deps.items():assert sha((ROOT/p).read_bytes())==h,p
    out={'scope':'Read-only aggregate supplements of the same two Friendly/global-box proofs, including exact common-denominator one-row certificates with zero rounding.',
      'files':files,'file_count':len(files),'total_bytes':sum(f['bytes'] for f in files),
      'dependency_global_box_manifest':item('research-goal-20261016/cover-cross-moment-global-box-files.json'),
      'external_source_dependencies_sha256':deps,'single_round_replay_passed':True,'exact_LCM_replay_passed':True,
      'exact_LCM_denominator_digits':[51,54],'exact_LCM_rounding_operations':0,'strict_local_integer_systems':2,
      'new_cell_exclusions':0,'actual_Lean_exclusions_instantiated_here':0,'complete_global_cover':False,'new_zero_proportion_proven':False,'submission_ready':False}
    p=HERE/'cover-cross-moment-aggregate-files.json';p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'manifest':p.relative_to(ROOT).as_posix(),'sha256':sha(p.read_bytes()),'files':len(files),'bytes':out['total_bytes']}),flush=True)
if __name__=='__main__':main()
