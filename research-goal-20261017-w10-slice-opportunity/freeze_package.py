"""Freeze the sole read-only whole-W10 support-domain opportunity audit.

Only hashes, scope and the already completed producer/independent receipts
are checked. No geometry traversal, lower-bound check, new witness, curve,
optimization, codec or Lean operation is performed by this finalizer.
"""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
AUDIT = ROOT / 'research-goal-20261017-w10-slice-opportunity-audit'
OUT = HERE / 'opportunity-files.json'


def record(path):
    return {'path': path.relative_to(ROOT).as_posix(),
            'bytes': path.stat().st_size,
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


assert not OUT.exists(), 'Refuse to replace a frozen manifest'
assert (AUDIT / 'audit-files.json').exists()
summary = json.loads((HERE / 'opportunities.json').read_bytes())
monitor = json.loads((HERE / 'monitor.json').read_bytes())
assert summary['complete_one_geometry_and_support_pass']
assert summary['counts']['branches'] == 95778
assert summary['parents_completed'] == 90000  # last periodic progress checkpoint
assert summary['parent_records']['uncompressed_bytes'] == 12 + 95778*118
assert summary['candidate_count'] == 191392
assert summary['source_sha256_start'] == summary['source_sha256_end']
assert summary['all_inputs_unchanged']
assert monitor['source_sha256_start'] == monitor['source_sha256_end']
assert monitor['worker_processes_launched'] == 1
assert monitor['worker_exit_code'] == 0 and monitor['termination_reason'] is None
assert monitor['observed_peak_working_set_bytes'] < monitor['memory_limit_bytes']
for key in ['solver_calls', 'oracle_calls', 'integer_floor_checks',
            'actual_kernel_evaluations', 'new_witnesses', 'new_partitions',
            'codec_generation_calls', 'Lean_invocations', 'mathematical_merges_proven']:
    assert summary[key] == 0, (key, summary[key])
assert not summary['complete_source_proven_feasible']
assert not summary['new_unconditional_zero_proportion_proven']
assert summary['J0_candidate_count_not_a_slice_opportunity'] == 5737

files = sorted([p for p in HERE.iterdir() if p.is_file() and p != OUT] +
               [p for p in AUDIT.iterdir() if p.is_file()],
               key=lambda p: p.relative_to(ROOT).as_posix())
assert all(p.stat().st_size < 4*1024**2 for p in files)
assert not any(p.name.endswith('.partial') for p in files)
package_names = {p.relative_to(ROOT).as_posix() for p in files}
deps = {}
reconstructed = {}
cache_names = {'research-goal-20261016/w10-size-audit-20261017/' + name
               for name in ['nodes.bin', 'fs.bin', 'treecodes.bin']}


def bind(row):
    name = row['path']
    actual = record(ROOT / name)
    assert actual['sha256'] == row['sha256'], name
    if 'bytes' in row:
        assert actual['bytes'] == row['bytes'], name
    assert not name.startswith('tmp/'), name
    if name not in package_names:
        (reconstructed if name in cache_names else deps)[name] = actual


for doc in [summary, monitor]:
    for name, digest in doc['source_sha256_start'].items():
        bind({'path': name, 'sha256': digest})
for item in [summary['parent_records']] + summary['prefix_files']:
    bind(item)

# The independent pin closes its input/source/receipt hashes. Its receipt
# need not share producer implementation or perform a mathematical floor check.
audit_pin = json.loads((AUDIT / 'audit-files.json').read_bytes())
assert audit_pin['passed'] and audit_pin['all_parent_records_checked']
for group in ['files', 'package_files', 'dependency_files',
              'reconstructed_dependency_files']:
    for row in audit_pin.get(group, []):
        bind(row)

# The already published zero-merge packet restores the exact three caches.
# Its large combined output and raw caches are verified but are not staged
# as duplicate raw files. Existing parts are enough for lossless restoration.
rest_dir = ROOT / 'research-goal-20261016/w10-size-merge-20261017'
rest = json.loads((rest_dir / 'restore-inputs.json').read_bytes())
for name in ['restore_inputs.py', 'restore-inputs.json']:
    bind(record(rest_dir / name))
for entry in rest['outputs']:
    for part in entry['parts']:
        bind({'path': (rest_dir / part['name']).relative_to(ROOT).as_posix(),
              'bytes': part['bytes'], 'sha256': part['sha256']})

assert not package_names & set(deps)
assert not package_names & set(reconstructed)
assert not set(deps) & set(reconstructed)
result = {
    'scope': __doc__,
    'package_files': [record(p) for p in files],
    'dependency_files': [deps[k] for k in sorted(deps)],
    'reconstructed_dependency_files': [reconstructed[k] for k in sorted(reconstructed)],
    'reconstructed_cache_restore_command':
        'python -S research-goal-20261016/w10-size-merge-20261017/restore_inputs.py',
    'producer_processes_launched': 1,
    'producer_PID': monitor['PID'],
    'producer_exit_code': 0,
    'producer_peak_RSS_bytes': monitor['observed_peak_working_set_bytes'],
    'parent_count': 95778,
    'producer_last_periodic_parent_progress_checkpoint': 90000,
    'candidate_count': 191392,
    'J0_candidates_excluded_from_slice_opportunities': 5737,
    'independent_whole_tree_support_and_statistics_replay_passed': True,
    'original_numeric_integer_floor_replayed_here': False,
    'source_attribution_is_a_new_decodable_stream': False,
    'new_curve_payload_known': False,
    'new_source_proven_feasible': False,
    'new_mathematical_merges': 0,
    'new_curves_or_witnesses': 0,
    'new_optimizer_or_oracle_calls': 0,
    'Lean_invocations': 0,
    'complete_global_cover_proven_by_this_audit': False,
    'new_unconditional_zero_proportion_proven': False,
    'website_submission_ready': False,
    'this_opportunity_family_stopped_no_automatic_pilot': True,
    'monitor_docstring_copy_typo_disclosed_in_NOTE': True,
    'mutable_governance_state_is_a_mathematical_premise': False,
}
OUT.write_text(json.dumps(result, indent=2, allow_nan=False)+'\n', encoding='utf8')
print(json.dumps({'manifest_sha256': record(OUT)['sha256'],
                  'package_files': len(files),
                  'package_bytes': sum(p.stat().st_size for p in files),
                  'largest_package_file_bytes': max(p.stat().st_size for p in files),
                  'dependencies': len(deps), 'reconstructed_dependencies': len(reconstructed)}))
