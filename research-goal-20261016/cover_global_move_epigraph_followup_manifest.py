"""Freeze nine verified new global-move chains and the completed family pilot."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).parent

def main():
    names=['cover-global-move-epigraph.json','cover-global-move-epigraph-replay.json',
      'cover_global_move_epigraph_archive.py','cover_global_move_epigraph_archive_replay.py',
      'cover_global_move_portfolio.py','cover_global_move_portfolio_verify.py','cover-global-move-portfolio-pilot.json',
      'cover_global_move_epigraph_followup_note.md',Path(__file__).name]
    names.extend('cover-global-move-epigraph-evidence/'+p.name for p in sorted((HERE/'cover-global-move-epigraph-evidence').iterdir()) if p.is_file())
    files={name:{'bytes':(HERE/name).stat().st_size,'sha256':hashlib.sha256((HERE/name).read_bytes()).hexdigest()} for name in names}
    out={'scope':__doc__,'files':files,'file_count':len(files),'total_bytes':sum(r['bytes'] for r in files.values()),
      'new_verified_global_move_chains':9,'combined_topmost_global_move_chains':24,'combined_old_branches_covered':251,
      'joint7_overlap':0,'direct_multi_move_pilot_cells':100,'direct_multi_move_pilot_new_exclusions':0,
      'ongoing_global_cut_contractor_excluded':True,'all_live_main_checkpoints_excluded':True,
      'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,'new_zero_proportion_proven':False,'final_website_submission_ready':False}
    target=HERE/'cover-global-move-epigraph-followup-files.json';target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'manifest':target.name,'file_count':len(files),'total_bytes':out['total_bytes'],'sha256':hashlib.sha256(target.read_bytes()).hexdigest()}))
if __name__=='__main__':main()
