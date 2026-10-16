"""Freeze only completed compact nineteen-region proof material."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).parent
sha=lambda b:hashlib.sha256(b).hexdigest()

def main():
    dest=HERE/'cover-global-cut-union-evidence';receipt=json.loads((dest/'independent-replay.json').read_bytes())
    assert receipt['all_passed'] and receipt['counts']['closed']==19
    control=json.loads((HERE/'cover-global-cut-full-control.json').read_bytes())
    summary={'scope':'Diagnostic paired energy-only control; final leaf witnesses not stored.',
      'source_sha256':sha((HERE/'cover-global-cut-full-control.json').read_bytes()),'receipt':control['receipt'],
      'control_closed_paths':[r['path'] for r in control['rows'] if r['control_result']],
      'global_closed_paths':[r['path'] for r in control['rows'] if r['global_cut_result']],
      'independent_control_terminal_leaf_replay_passed':False}
    (HERE/'cover-global-cut-full-control-summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf8')
    names=['cover_global_cut_full_contractor.py','cover_global_cut_full_verify.py','cover_global_cut_full_control.py',
      'cover_make_full_global_cut.py','cover-global-cut-full-contractor-replay.json','cover-global-cut-full-control-summary.json',
      'cover_global_cut_hypograph.py','cover_global_cut_hypograph_verify.py','cover_global_cut_hypograph_probe.py',
      'cover_global_cut_hypograph_probe_verify.py','cover-global-cut-hypograph-replay.json',
      'cover_global_cut_intersection.py','cover_global_cut_intersection_verify.py','cover-global-cut-intersection-replay.json',
      'cover_global_cut_codec.py','cover_global_cut_archive.py','cover_global_cut_archive_replay.py',
      'cover_global_cut_union_note.md',Path(__file__).name]
    names.extend('cover-global-cut-union-evidence/'+p.name for p in sorted(dest.iterdir()) if p.is_file())
    files={name:{'bytes':(HERE/name).stat().st_size,'sha256':sha((HERE/name).read_bytes())} for name in names}
    out={'scope':__doc__,'files':files,'file_count':len(files),'total_bytes':sum(r['bytes'] for r in files.values()),
      'new_topmost_global_cut_regions':19,'prior_finite_move_regions':24,'combined_topmost_global_regions':43,
      'new_old_branches_covered':307,'combined_old_branches_covered':558,'joint7_overlap':0,
      'all_live_checkpoints_excluded':True,'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,
      'new_zero_proportion_proven':False,'final_website_submission_ready':False}
    path=HERE/'cover-global-cut-union-files.json';path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'manifest':path.name,'file_count':len(files),'total_bytes':out['total_bytes'],'sha256':sha(path.read_bytes())}))
if __name__=='__main__':main()
