"""Read-only binding of the stopped main's last complete atomic snapshot.

The original tool handle is unavailable, not a source of an exit code.
Host process absence is the trusted parent task's elevated-CIM observation.
Read one shared-delete handle, hash all bytes, inspect JSON header/tail and
frontier DBMs. No full semantic replay, migration, restart or copy is made.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, time
from cover_compact_checkpoint import open_snapshot

HERE = Path(__file__).parent
ROOT = HERE.parent
PAIRS = [(i, i+1) for i in range(9)]+[(i, j) for i in range(9) for j in range(i+2, 10)]


def closed(state):
    lo, hi = state
    assert len(lo) == len(hi) == 45 and all(isinstance(v, int) for v in lo+hi)
    assert all(l <= u for l, u in zip(lo, hi))
    matrix = [[0]*10 for _ in range(10)]
    for (i, j), l, u in zip(PAIRS, lo, hi):
        matrix[i][j] = u;matrix[j][i] = -l
    assert all(matrix[i][j] <= matrix[i][k]+matrix[k][j]
               for i in range(10) for j in range(10) for k in range(10))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args();assert not args.output.exists(), 'Use a new receipt.'
    started = time.monotonic();path = HERE/'window-compact-obbt-cover.json'
    before = path.stat();digest = hashlib.sha256();size = 0
    with open_snapshot(path.resolve()) as f:
        head = f.read(65536);marker = b'"accepted":[';at = head.index(marker)
        metadata = json.loads((head[:at].rstrip(b',')+b'}').decode())
        f.seek(0, 2);expected_size = f.tell();f.seek(max(0, expected_size-(8<<20)))
        tail = f.read().decode();at = tail.rfind('"unresolved":');assert at >= 0
        frontier, end = json.JSONDecoder().raw_decode(tail[at+len('"unresolved":'):])
        at = tail.rfind('"tangent_data":');assert at >= 0
        supports, end = json.JSONDecoder().raw_decode(tail[at+len('"tangent_data":'):])
        assert tail[at+len('"tangent_data":')+end:].strip() == '}'
        assert len(frontier) == metadata['unresolved_count'] and sum(metadata['counts'].values()) == metadata['accepted_count']
        for row in frontier:
            assert row['depth'] == len(row['path'])-1 and set(row['path'][1:]) <= {'0', '1'}
            closed(row['state'])
        paths = {r['path'] for r in frontier};assert len(paths) == len(frontier)
        assert not any(p != q and q.startswith(p) for p in paths for q in paths)
        ancestors = {p[:k] for p in paths for k in range(1, len(p))}
        complete = sorted({p+bit for p in ancestors for bit in '01'
                           if p+bit not in ancestors and p+bit not in paths}, key=lambda p: (len(p), p))
        f.seek(0)
        while True:
            chunk = f.read(1<<20)
            if not chunk:
                break
            digest.update(chunk);size += len(chunk)
    after = path.stat();assert size == expected_size == before.st_size == after.st_size
    assert before.st_mtime_ns == after.st_mtime_ns
    guards = metadata['input_sha256']
    assert all(hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == expected for name, expected in guards.items())
    launch = json.loads((HERE/'cover-main-recovery117500-launch.json').read_bytes())
    endpoint = launch['resume_checked']+launch['remaining_original_node_budget']
    assert metadata['checked'] <= endpoint
    result = {'scope': __doc__, 'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'recorded_UTC': datetime.now(timezone.utc).isoformat(),
      'old_session_id': 1700, 'old_PID': 46548,
      'tool_poll_result': 'write_stdin failed: Unknown process id1700',
      'tool_terminal_exit_code_available': False, 'exit_code': None,
      'last_available_stdout': '{"checked":130600,"accepted":65290,"pending":21,"contraction_paths":22965,"sublevel_paths":88379,"seconds":2222.2183716999934}',
      'parent_host_observation': {'source': 'Trusted parent message: two elevated-CIM observations at21:31UTC2026-10-16',
        'PID46548_absent': True, 'all_python_exe_absent': True},
      'search_is_not_live': True, 'exit_cause': 'unknown', 'OOM_evidence_obtained': False,
      'stderr_or_crash_log_obtained': False,
      'snapshot_path': path.relative_to(ROOT).as_posix(), 'snapshot_bytes': size,
      'snapshot_sha256': digest.hexdigest(),
      'snapshot_last_write_UTC': datetime.fromtimestamp(before.st_mtime, timezone.utc).isoformat(),
      'metadata': {k: metadata[k] for k in ['pid', 'checked', 'accepted_count', 'counts', 'unresolved_count',
        'maxdepth', 'seconds', 'contraction_paths', 'contraction_steps', 'sublevel_contraction_paths',
        'sublevel_bounds', 'resumed_from']},
      'all_frozen_input_hashes_matched': True, 'complete_header_and_final_JSON_tail_checked': True,
      'complete_middle_JSON_structure_or_witness_semantic_replay_performed': False,
      'frontier_DBM_closures_checked': len(frontier), 'frontier': frontier,
      'maximal_completed_prefixes': complete, 'support_records': len(supports),
      'no_domain_volume_or_remaining_work_percentage_inferred': True,
      'original_total_checked_budget_endpoint': endpoint,
      'remaining_original_node_budget_at_snapshot': endpoint-metadata['checked'],
      'hash_binds_bytes_but_no_immutable_copy_or_OS_readonly_attribute_created': True,
      'handoff_or_restart_started': False, 'new_zero_proportion_proven': False,
      'seconds': time.monotonic()-started}
    args.output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf8')
    print(json.dumps({k: result[k] for k in ['snapshot_bytes', 'snapshot_sha256', 'snapshot_last_write_UTC',
      'metadata', 'support_records', 'remaining_original_node_budget_at_snapshot', 'seconds']}), flush=True)


if __name__ == '__main__':
    main()
