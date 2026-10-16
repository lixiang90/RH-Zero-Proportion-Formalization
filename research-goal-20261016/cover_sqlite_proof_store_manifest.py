"""Pin only small source/test/roundtrip evidence; exclude large local stores."""
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
    load = lambda name: json.loads((HERE/name).read_bytes())
    imported = load('cover-sqlite-store132000-import.json')
    replayed = load('cover-sqlite-store132000-independent-replay.json')
    toy = load('cover-sqlite-store-toy-tests.json')
    local = load('cover-sqlite-store132000-local-binding.json')
    assert imported['source_sha256'] == toy['producer_sha256'] == sha((HERE/'cover_sqlite_proof_store.py').read_bytes())
    assert replayed['source_sha256'] == toy['independent_replay_source_sha256'] == sha((HERE/'cover_sqlite_proof_store_replay.py').read_bytes())
    assert toy['source_sha256'] == sha((HERE/'cover_sqlite_proof_store_test.py').read_bytes()) and toy['all_passed']
    assert imported['baseline']['source_sha256'] == replayed['source_snapshot_sha256'] == local['baseline_source_sha256']
    assert imported['baseline']['canonical_document_sha256'] == replayed['canonical_document_sha256'] == local['baseline_canonical_document_sha256']
    assert replayed['all_entry_payloads_orders_and_hashes_matched'] and replayed['post_baseline_node_transactions_present'] == 0
    assert local['journal_sequence'] == 0 and local['actual_search_nodes_appended'] == 0
    names = ['cover_sqlite_proof_store.py', 'cover_sqlite_proof_store_replay.py',
      'cover_sqlite_proof_store_test.py', 'cover-sqlite-store-toy-tests.json',
      'cover-sqlite-store132000-import.json', 'cover-sqlite-store132000-independent-replay.json',
      'cover-sqlite-store132000-local-binding.json', 'cover_sqlite_proof_store_note.md', Path(__file__).name]
    files = [record(HERE/name) for name in names]
    deps = [HERE/name for name in ['cover_compact_checkpoint.py', 'cover_compact_codec.py',
      'cover_correlated_replay.py', 'cover_contractor_verify.py', 'cover_flow_basis.py',
      'cover_correlated_verify.py']]+[ROOT/'research-20261016-w10-cert/independent_integer_audit.py']
    manifest = {'scope': __doc__, 'files': files, 'file_count': len(files),
      'total_bytes': sum(r['bytes'] for r in files),
      'already_existing_source_dependencies': [record(p) for p in deps],
      'stopped_snapshot_evidence_manifest': record(HERE/'cover-main-stopped-files.json'),
      'excluded_large_local_database': local,
      'excluded_original_snapshot': {'path': 'research-goal-20261016/window-compact-obbt-cover.json',
        'bytes': imported['baseline']['source_bytes'], 'sha256': imported['baseline']['source_sha256']},
      'excluded_toy_runtime_folder': 'research-goal-20261016/sqlite-store-toy/',
      'independent_unit_roundtrip_passed': True,
      'units_checked': replayed['canonical_units_independently_compared'],
      'real_process_crash_and_rollback_test_passed': toy['actual_os_exit_before_commit_returncode'] == 77,
      'import_peak_working_set_bytes': imported['process_peak_working_set_bytes'],
      'bounded_storage_only_not_live_engine_RSS_claim': True,
      'actual_cover_producer_adopted': False, 'actual_search_nodes_appended': 0,
      'baseline_semantic_witness_replay': False, 'new_search_started': False,
      'new_zero_proportion_proven': False}
    args.output.write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf8')
    print(json.dumps({'path': str(args.output), 'sha256': sha(args.output.read_bytes()),
      'files': len(files), 'bytes': manifest['total_bytes']}), flush=True)


if __name__ == '__main__':
    main()
