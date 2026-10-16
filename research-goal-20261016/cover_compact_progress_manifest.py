"""Pin the small reviewed artifacts; exclude evolving large search checkpoints."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).parent

def main():
    names=['cover_correlated_curvature.py','cover_correlated_curvature_verify.py',
      'cover-correlated-curvature.json','cover-correlated-curvature-replay.json',
      'cover-correlated-curvature-newton.json','cover-correlated-curvature-newton-replay.json',
      'cover_joint_after_obbt.py','cover_joint_after_obbt_verify.py','cover-joint-after-obbt.json','cover-joint-after-obbt-replay.json',
      'cover_compact_codec.py','cover_compact_checkpoint.py','cover_compact_pilot.py','cover_make_compact_variant.py','cover_make_guarded_variant.py',
      'window_compact_obbt_cover.py','window_compact_obbt_guarded_cover.py','window_compact_obbt_replay.py',
      'cover-compact-variant-generated.json','cover-compact-guarded-generated.json',
      'cover_compact_runtime_archive.py','cover_compact_runtime_archive_replay.py','cover_compact_runtime_note.md',
      'window-compact-obbt-pilot.replay.json','window-compact-obbt-resume-pilot-replay.json',
      'window-compact-obbt-migration.conversion.json','window-compact-obbt-migration22500.conversion.json',
      'window-compact-obbt-migration22500-replay.json',Path(__file__).name]
    names.extend('cover-compact-runtime-evidence/'+p.name for p in sorted((HERE/'cover-compact-runtime-evidence').iterdir()) if p.is_file())
    files={name:{'bytes':(HERE/name).stat().st_size,'sha256':hashlib.sha256((HERE/name).read_bytes()).hexdigest()} for name in names}
    out={'scope':__doc__,'files':files,'file_count':len(files),'total_bytes':sum(row['bytes'] for row in files.values()),
      'live_checkpoint_excluded':True,'migration22500_independent_replay_pending':False,
      'migration22500_independent_replay_passed':True,
      'main_runner_session_owned_by_cover_agent':69821,'main_resumed_from_checked':22500,
      'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,'new_zero_proportion_proven':False,'final_website_submission_ready':False}
    target=HERE/'cover-compact-progress-files.json';target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps({'manifest':target.name,'file_count':len(files),'total_bytes':out['total_bytes'],'sha256':hashlib.sha256(target.read_bytes()).hexdigest()}))
if __name__=='__main__':main()
