"""Freeze the global-u/q box variant without changing the prior factor pin."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).parent;ROOT=HERE.parent;sha=lambda b:hashlib.sha256(b).hexdigest()
NAMES=['cover_cross_moment_global_box.py','cover_cross_moment_global_box_replay.py',
  'cover_cross_moment_global_box_note.md','cover_cross_moment_global_box_manifest.py',
  'cover-cross-moment-global-box-cases.json']
NAMES += ['cover-cross-moment-global-box-evidence/'+n for n in ['proof.json.gz','comparison.json.gz','manifest.json','independent-replay.json']]


def item(path):
    p=ROOT/path;b=p.read_bytes();return {'path':path,'bytes':len(b),'sha256':sha(b)}


def main():
    folder=HERE/'cover-cross-moment-global-box-evidence';r=json.loads((folder/'independent-replay.json').read_bytes());m=json.loads((folder/'manifest.json').read_bytes())
    assert r['all_checks_passed'] and r['strict_local_integer_systems']==2 and r['tight_derivative_box_queries_required']==0
    assert r['script_sha256']==sha((HERE/'cover_cross_moment_global_box_replay.py').read_bytes())
    assert r['proof_gzip_sha256']==m['proof_gzip_sha256'] and r['comparison_gzip_sha256']==m['comparison_gzip_sha256']
    files=[item('research-goal-20261016/'+n) for n in NAMES];own={f['path'] for f in files}
    dependencies={p:h for p,h in r['dependency_sources_sha256'].items() if p not in own}
    for p,h in dependencies.items():assert sha((ROOT/p).read_bytes())==h,p
    data=['research-goal-20261016/cover_newjet.json','research-20261016-followup/window_reweight_rational.json',
      'research-goal-20261016/window-moment-friendly-packets.json','research-goal-20261016/cover-curvature-actual-active.json']
    out={'scope':'Same frozen two Friendly grouped certificates rechecked using global +/-7 u/q boxes; no new exclusions.',
      'files':files,'file_count':len(files),'total_bytes':sum(f['bytes'] for f in files),
      'dependency_factor_manifest':item('research-goal-20261016/cover-cross-moment-factor-files.json'),
      'external_source_dependencies_sha256':dependencies,'external_data_dependencies':[item(p) for p in data],
      'box_policy':r['box_policy'],'all_factors_energy_weights_and_unrounded_rows_unchanged':True,
      'independent_global_box_replay_passed':True,'strict_local_integer_systems':2,'tight_derivative_box_queries_required':0,
      'new_cell_exclusions':0,'actual_Lean_exclusions_instantiated_here':0,'complete_global_cover':False,'new_zero_proportion_proven':False,'submission_ready':False}
    p=HERE/'cover-cross-moment-global-box-files.json';p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'manifest':p.relative_to(ROOT).as_posix(),'sha256':sha(p.read_bytes()),'files':len(files),'bytes':out['total_bytes']}),flush=True)
if __name__=='__main__':main()
