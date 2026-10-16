"""Freeze completed global-move mathematics; exclude the live 300-cell joint run."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).parent

def main():
    names=['cover_integer_move.py','cover_integer_move_verify.py','cover_integer_move_concave.py','cover_integer_move_concave_verify.py',
      'cover-integer-move-concave.json','cover-integer-move-concave-replay.json',
      'cover_global_move_epigraph.py','cover_global_move_epigraph_verify.py',
      'cover-global-move-epigraph-pilot.json','cover-global-move-epigraph-pilot-replay.json',
      'cover_global_move_archive.py','cover_global_move_archive_replay.py',
      'cover_floor_complexity_probe.py','cover-floor-complexity-884.json','cover-floor-complexity-880.json','cover-floor-complexity-8785.json',
      'cover_global_move_note.md',Path(__file__).name]
    names.extend('cover-global-move-evidence/'+p.name for p in sorted((HERE/'cover-global-move-evidence').iterdir()) if p.is_file())
    files={name:{'bytes':(HERE/name).stat().st_size,'sha256':hashlib.sha256((HERE/name).read_bytes()).hexdigest()} for name in names}
    out={'scope':__doc__,'files':files,'file_count':len(files),'total_bytes':sum(r['bytes'] for r in files.values()),
      'signed_difference_move_chains_verified':15,'old_branches_covered':141,'joint_gradient7_overlap':0,
      'sublevel_global_move_pilot_chains_verified':1,'three_floor_one_level_sample_size':300,
      'live_300_cell_epigraph_output_excluded':True,'all_evolving_main_checkpoints_excluded':True,
      'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,'new_zero_proportion_proven':False,'final_website_submission_ready':False}
    target=HERE/'cover-global-move-progress-files.json';target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'manifest':target.name,'file_count':len(files),'total_bytes':out['total_bytes'],'sha256':hashlib.sha256(target.read_bytes()).hexdigest()}))
if __name__=='__main__':main()
