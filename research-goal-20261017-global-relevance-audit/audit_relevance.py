"""Read-only global relevance audit of the fixed sextic test cell.

Check the frozen database hash, export its exact target-subtree records and
current frontier, and check binary prefix topology. This does not replay
the historical baseline's mathematical certificates or prove a global floor.
No search, oracle, optimizer, compiler, or database mutation is performed.
"""
from pathlib import Path
from fractions import Fraction
import gzip, hashlib, json, sqlite3, time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
DB = ROOT / 'research-goal-20261016/sqlite-bounded143004/campaign.sqlite'
PROGRESS = ROOT / 'research-goal-20261016/sqlite-bounded143004/progress.json'
EPOCH = ROOT / 'research-goal-20261016/sqlite-bounded143004/epoch.json'
MODEL = ROOT / 'research-goal-20261017-actual-sextic-static/actual-sextic.json.gz'
EXACT_PIN = ROOT / 'research-goal-20261017-actual-sextic-exact-ray/exact-ray-files.json'
OUT = HERE / 'global-relevance.json'


def sha_file(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda: f.read(4 * 1024 * 1024), b''):
            h.update(b)
    return h.hexdigest()


def main():
    assert not OUT.exists(), 'Do not overwrite a frozen receipt'
    started = time.monotonic()
    sources = [Path(__file__), PROGRESS, EPOCH, MODEL, EXACT_PIN]
    pins = {p.relative_to(ROOT).as_posix(): sha_file(p) for p in sources}
    progress = json.loads(PROGRESS.read_bytes())
    epoch = json.loads(EPOCH.read_bytes())
    model = json.loads(gzip.decompress(MODEL.read_bytes()))
    target = model['path']
    assert target == 'r001000001000100110011001'
    assert model['target'] == epoch['target'] == '11/1250'
    expected_db = progress['database_sha256']
    size = DB.stat().st_size
    assert size == progress['database_bytes']
    before = sha_file(DB)
    assert before == expected_db
    db = sqlite3.connect(DB.resolve().as_uri() + '?mode=ro', uri=True)
    assert db.execute('PRAGMA query_only=ON').fetchone() is None
    frontier = []
    for position, path, payload, digest in db.execute(
            'SELECT position,path,payload,digest FROM frontier ORDER BY position'):
        assert hashlib.sha256(payload).hexdigest() == digest
        value = json.loads(payload)
        assert value['path'] == path
        frontier.append(dict(position=position, path=path, payload_sha256=digest,
                             payload=value, payload_bytes=len(payload)))
    related = [r['path'] for r in frontier
               if r['path'].startswith(target) or target.startswith(r['path'])]
    assert len(frontier) == progress['final_state']['unresolved_count'] == 17
    rows = []
    for section, position, path, payload, digest in db.execute(
            'SELECT section,position,item_key,payload,digest FROM entries '
            'WHERE item_key=? OR item_key LIKE ? ORDER BY section,position',
            (target, target + '%')):
        assert path.startswith(target)
        assert hashlib.sha256(payload).hexdigest() == digest
        rows.append(dict(section=section, position=position, path=path,
                         payload_sha256=digest, payload_bytes=len(payload),
                         payload=json.loads(payload)))
    leaves = {r['path'] for r in rows if r['section'] == 'accepted'}
    branches = {r['path'] for r in rows if r['section'] == 'branches'}
    seen = set()

    def visit(path):
        assert path not in seen
        seen.add(path)
        assert (path in leaves) != (path in branches)
        if path in branches:
            visit(path + '0')
            visit(path + '1')

    visit(target)
    assert seen == leaves | branches and len(leaves) == 5 and len(branches) == 4
    kraft = sum((Fraction(1, 2 ** (len(p) - len(target))) for p in leaves), Fraction(0))
    assert kraft == 1 and not related
    journal = db.execute('SELECT sequence,path FROM node_log '
                         'WHERE path=? OR path LIKE ? ORDER BY sequence',
                         (target, target + '%')).fetchall()
    assert journal == []
    # Quantify ancestor relevance with record counts/bytes, not geometric
    # volume or remaining work. Only the C ancestry is inspected here.
    ancestors = {target[:n]: {} for n in range(1, len(target) + 1)}
    for section, path, count_bytes in db.execute(
            "SELECT section,item_key,length(payload) FROM entries WHERE section "
            "IN ('accepted','branches','contractions','sublevel_contractions')"):
        for n in range(1, min(len(path), len(target)) + 1):
            prefix = path[:n]
            if prefix in ancestors:
                value = ancestors[prefix].setdefault(section, [0, 0])
                value[0] += 1
                value[1] += count_bytes
    ancestor_stats = []
    for path, counts in ancestors.items():
        ancestor_stats.append(dict(path=path, record_counts_and_JSON_bytes=counts,
            frontier_descendants=[r['path'] for r in frontier if r['path'].startswith(path)]))
    db.close()
    after = sha_file(DB)
    assert after == before and DB.stat().st_size == size
    assert pins == {p.relative_to(ROOT).as_posix(): sha_file(p) for p in sources}
    summary = {s: dict(records=sum(r['section'] == s for r in rows),
                      payload_bytes=sum(r['payload_bytes'] for r in rows if r['section'] == s))
               for s in sorted({r['section'] for r in rows})}
    receipt = dict(scope=__doc__, passed=True, source_sha256=pins,
        database_path=DB.relative_to(ROOT).as_posix(), database_bytes=size,
        database_sha256_before=before, database_sha256_after=after,
        database_unchanged=True, opened_readonly_and_queryonly=True,
        target=target, floor=model['target'], current_frontier=frontier,
        related_frontier=related, target_records=rows, target_record_summary=summary,
        binary_subtree_leaves=sorted(leaves), binary_subtree_branches=sorted(branches),
        binary_prefix_topology_complete=True, kraft_sum=str(kraft),
        matching_new_journal_nodes=journal, in_imported_historical_baseline=True,
        ancestor_record_inventory=ancestor_stats,
        exact_sextic_result_closes_new_frontier=False,
        source_compression_benefit_from_replacing_this_subtree_proved=False,
        historical_baseline_mathematics_replayed=False,
        actual_Lean_cell_exclusion_proved=False, complete_global_cover=False,
        new_unconditional_zero_proportion_proven=False, website_submission_ready=False,
        elapsed_seconds=time.monotonic() - started)
    OUT.write_text(json.dumps(receipt, indent=2, allow_nan=False) + '\n', encoding='utf8')
    print(json.dumps(dict(passed=True, database_sha256=before,
        target=target, accepted_leaves=len(leaves), branches=len(branches),
        frontier_count=len(frontier), related_frontier=related,
        target_record_summary=summary, elapsed_seconds=receipt['elapsed_seconds'])))


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled')
    main()
