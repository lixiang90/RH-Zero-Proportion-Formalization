"""Freeze targeted curvature proofs, their ancestry, and completed diagnostics."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
    folder=HERE/'cover-targeted-curvature-evidence';proof=json.loads((folder/'independent-three-replay.json').read_bytes())
    assert proof['all_passed'] and len(proof['verified'])==3
    names=['cover_targeted_quadratic_gradient.py','cover-targeted-quadratic-gradient.json',
      'cover_targeted_curvature_verify.py','cover-targeted-curvature-replay.json',
      'cover_targeted_curvature_archive.py','cover_targeted_curvature_archive_replay.py',
      'cover_targeted_curvature_crossprobe.py','cover-targeted-curvature-crossprobe.json',
      'cover_targeted_curvature_cross_verify.py','cover-targeted-curvature-cross-replay.json',
      'cover_targeted_curvature_three_replay.py','cover-current-frontier-20261017b.json',
      'cover_frontier_basin_diagnostic.py','cover-frontier-basin-diagnostic.json',
      'cover_frontier_well_diagnostic.py','cover-frontier-well-diagnostic.json',
      'cover_targeted_curvature_note.md',Path(__file__).name]
    names.extend('cover-targeted-curvature-evidence/'+p.name for p in sorted(folder.iterdir()) if p.is_file())
    files={name:{'bytes':(HERE/name).stat().st_size,'sha256':sha((HERE/name).read_bytes())} for name in names}
    out={'scope':__doc__,'files':files,'file_count':len(files),'total_bytes':sum(v['bytes'] for v in files.values()),
      'fixed_frontier_cells':6,'verified_uniform_negative_curvature_cells':3,'new_quadratic_gradient_exclusions':0,
      'new_branch_savings_independently_established':False,'all_live_checkpoints_excluded':True,
      'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,'new_zero_proportion_proven':False,'final_website_submission_ready':False}
    path=HERE/'cover-targeted-curvature-files.json';path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'manifest':path.name,'file_count':len(files),'total_bytes':out['total_bytes'],'sha256':sha(path.read_bytes())}))
if __name__=='__main__':main()
