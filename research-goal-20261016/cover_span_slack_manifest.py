"""Freeze the bounded affine-slack RLT experiment and exact finite replay."""
from pathlib import Path
import argparse, hashlib, json

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
    default_raw = (HERE/'cover-span-slack-first-case.json').read_bytes();default = json.loads(default_raw)
    ipm_raw = (HERE/'cover-span-slack-first-case-ipm.json').read_bytes();ipm = json.loads(ipm_raw)
    replay = json.loads((HERE/'cover-span-slack-independent-replay.json').read_bytes())
    assert replay['passed_exact_new_factor_and_old_atom_algebra']
    assert replay['default_run_sha256'] == ipm['frozen_default_run_sha256'] == sha(default_raw)
    assert replay['IPM_run_sha256'] == sha(ipm_raw)
    assert default['history'][-1]['LP_status'] == 1 and default['integer_certificate'] is None
    assert ipm['LP']['status'] == 0 and ipm['LP']['energy_slack_hint'] == 0
    assert ipm['strict_integer_certificate'] is None
    names = ['cover_span_slack_separator.py', 'cover_span_slack_probe.py',
      'cover-span-slack-first-case.json', 'cover_span_slack_ipm_probe.py',
      'cover-span-slack-first-case-ipm.json', 'cover_span_slack_audit.py',
      'cover-span-slack-old-atoms.json', 'cover-span-slack-independent-replay.json',
      'cover_span_slack_note.md', Path(__file__).name]
    files = [record(HERE/name) for name in names]
    deps = ['cover_cross_moment_probe.py', 'cover_lifted_graph_probe.py',
      'cover_cross_moment_exact_rows.py', 'cover_cross_moment_factor_replay.py',
      'cover_cross_moment_old_rows_replay.py', 'cover_exact_scalar_replay.py',
      'cover_lifted_graph_verify.py', 'cover_newjet.json',
      'cover-cross-moment-remaining-files.json', 'cover-cross-moment-remaining-six.json']
    manifest = {'scope': __doc__, 'files': files, 'file_count': len(files),
      'total_bytes': sum(r['bytes'] for r in files),
      'existing_dependencies': [record(HERE/name) for name in deps],
      'parameters': record(ROOT/'research-20261016-followup/window_reweight_rational.json'),
      'discovery_seed_raw_alternative': 'The already frozen remaining-six standalone proof contains the same records. Its standalone replay proves ancestry and energy0 provenance.',
      'path': default['path'], 'target': '11/1250', 'new_kernel_samples': 0,
      'new_energy_anchors': 0, 'new_variables': 0, 'new_cases': 1,
      'maximum_cut_rounds': 2, 'fixed_products_saved': 128, 'candidate_factors': 39,
      'default_final_outcome': '45-second timeout, inconclusive',
      'same128_cut_IPM_outcome': 'Approximate zero-slack primal; max floating row error7.14e-8; not exact feasibility.',
      'independent_old_atom_and_factor_algebra_replay_passed': True,
      'independent_replay_command': 'python -S -B -X utf8 research-goal-20261016/cover_span_slack_audit.py --output NEW_RECEIPT.json',
      'new_actual_Lean_factor_consumer_proven': False, 'strict_integer_exclusions': 0,
      'complete_global_cover': False, 'new_zero_proportion_proven': False,
      'main_search_or_frozen_sources_modified': False}
    args.output.write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf8')
    print(json.dumps({'path': str(args.output), 'sha256': sha(args.output.read_bytes()),
                      'files': len(files), 'bytes': manifest['total_bytes']}), flush=True)


if __name__ == '__main__':
    main()
