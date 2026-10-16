"""Pin small recovery/structure evidence, excluding both huge checkpoints.

The stream audit was made on the main filename while its complete contents
were the frozen117500 snapshot. Reproducing that full audit requires the
exact checkpoint bytes; neither huge immutable copy nor mutable output is
included here. The cone counterexample independently replays with Python-S
and no checkpoint. The structure JSON preserves all29 frontier states.
"""
from pathlib import Path
import argparse, datetime, hashlib, json

HERE = Path(__file__).parent
ROOT = HERE.parent
sha = lambda b: hashlib.sha256(b).hexdigest()


def record(path):
    raw = path.read_bytes()
    return {'path': path.relative_to(ROOT).as_posix(), 'bytes': len(raw), 'sha256': sha(raw)}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args();assert not args.output.exists(), 'Use a new manifest.'
    audit = json.loads((HERE/'cover-main-recovery117500-audit.json').read_bytes())
    launch = json.loads((HERE/'cover-main-recovery117500-launch.json').read_bytes())
    host = json.loads((HERE/'cover-main-recovery117500-host-confirmation.json').read_bytes())
    structure = json.loads((HERE/'cover-main117500-structure-review.json').read_bytes())
    cone = json.loads((HERE/'cover-span-slack-cone-replay.json').read_bytes())
    assert audit['checkpoint_sha256'] == launch['resume_checkpoint_sha256'] == host['resume_checkpoint_sha256'] == structure['audited_checkpoint_sha256']
    assert audit['checkpoint_bytes'] == launch['resume_checkpoint_bytes'] == 831108505
    assert cone['passed'] and cone['matches_frozen_structure_review']
    assert cone['review_sha256'] == sha((HERE/'cover-main117500-structure-review.json').read_bytes())
    assert cone['source_sha256'] == sha((HERE/'cover_span_slack_cone_replay.py').read_bytes())
    progress_path = HERE/'cover-main-recovery117500-observed-progress.json'
    assert not progress_path.exists()
    progress = {'scope': 'One authoritative tool-handle observation of the recovered existing main; no relaunch.',
      'recorded_UTC': datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'session_id': 1700, 'host_PID_from_prior_parent_CIM': 46548,
      'observation': 'write_stdin returned running session1700 with sequential progress118300..122400',
      'last_checked': 122400, 'accepted': 61189, 'pending': 23,
      'Newton_contraction_paths': 22234, 'OBBT_sublevel_paths': 82926,
      'last_elapsed_after_resume_seconds': 974.0946299999996,
      'live_at_observation_only': True, 'snapshot_semantic_certificate_replay_complete': False,
      'complete_global_cover': False, 'new_zero_proportion_proven': False}
    progress_path.write_text(json.dumps(progress, indent=2)+'\n', encoding='utf8')
    names = ['cover_main_recovery_audit.py', 'cover-main-recovery117500-audit.json',
      'cover-main-recovery117500-launch.json', 'cover-main-recovery117500-host-confirmation.json',
      'cover_main_structure_review.py', 'cover-main117500-structure-review.json',
      'cover_main_structure_review.md', 'cover_span_slack_cone_replay.py',
      'cover-span-slack-cone-replay.json', progress_path.name, Path(__file__).name]
    files = [record(HERE/name) for name in names]
    manifest = {'scope': __doc__, 'files': files, 'file_count': len(files),
      'total_bytes': sum(row['bytes'] for row in files),
      'large_checkpoint_excluded': {'path': 'research-goal-20261016/window-compact-obbt-recovery117500.json',
        'bytes': audit['checkpoint_bytes'], 'sha256': audit['checkpoint_sha256'],
        'required_only_to_regenerate_complete_stream_audit': True},
      'mutable_main_output_excluded': 'research-goal-20261016/window-compact-obbt-cover.json',
      'recovery_launch_command_sha256': launch['command_sha256'],
      'frozen_main_source_sha256': launch['script_sha256'],
      'trusted_parent_host_confirmation': {'single_writer_PID': 46548, 'old_PID36004_absent': True,
        'sandbox_process_enumeration_is_not_host_authority': True},
      'checkpoint_structural_audit_passed': audit['passed_complete_JSON_and_binary_prefix_tree'],
      'checkpoint_semantic_certificate_replay_complete': False,
      'known_69_basin_data_dependency': {'path': 'research-goal-20261016/cover-newwindow-gram.json',
        'sha256': structure['Gram_sha256'], 'already_existing_dependency': True},
      'static_review_frontier_cells': len(structure['frontier']),
      'cone_counterexample_independent_Python_S_replay_passed': True,
      'cone_replay_command': 'python -S -B -X utf8 research-goal-20261016/cover_span_slack_cone_replay.py --output NEW_RECEIPT.json',
      'prefixes_are_not_geometric_volume_or_completion_percentage': True,
      'new_actual_cell_exclusions': 0, 'complete_global_cover': False,
      'new_zero_proportion_proven': False}
    args.output.write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf8')
    print(json.dumps({'manifest': str(args.output), 'sha256': sha(args.output.read_bytes()),
                      'files': len(files), 'bytes': manifest['total_bytes']}), flush=True)


if __name__ == '__main__':
    main()
