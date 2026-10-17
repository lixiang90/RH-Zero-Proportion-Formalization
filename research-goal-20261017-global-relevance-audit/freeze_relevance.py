"""Freeze read-only relevance evidence; do not publish the large local DB."""
from pathlib import Path
import hashlib, json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OUT = HERE / 'relevance-files.json'


def row(path):
    raw = path.read_bytes()
    return dict(path=path.relative_to(ROOT).as_posix(), bytes=len(raw),
                sha256=hashlib.sha256(raw).hexdigest())


def main():
    assert not OUT.exists()
    receipt = json.loads((HERE / 'global-relevance.json').read_bytes())
    independent = ROOT / 'research-goal-20261017-global-relevance-independent/audit-files.json'
    assert row(independent)['sha256'] == '957a2523611f815ec94cab29f62e60f3ccf374faf3f9ce7c392dc7ff7eb0b86c'
    package = [HERE / s for s in ['audit_relevance.py', 'global-relevance.json',
                                  'NOTE.zh.md', 'freeze_relevance.py']]
    dependencies = [ROOT / s for s in receipt['source_sha256'] if s != package[0].relative_to(ROOT).as_posix()]
    dependencies.append(independent)
    for path, digest in receipt['source_sha256'].items():
        assert row(ROOT / path)['sha256'] == digest
    assert receipt['passed'] and receipt['database_unchanged']
    assert receipt['binary_prefix_topology_complete'] and receipt['kraft_sum'] == '1'
    assert len(receipt['binary_subtree_leaves']) == 5 and not receipt['related_frontier']
    value = dict(scope=__doc__, package_files=[row(p) for p in package],
        dependency_files=[row(p) for p in dependencies],
        local_database_evidence=dict(path=receipt['database_path'],
            bytes=receipt['database_bytes'], sha256=receipt['database_sha256_before'],
            published=False, verified_before_and_after_readonly=True),
        fixed_target_cell_already_recorded_closed=True,
        newly_closed_frontier_count=0, historical_baseline_math_replayed=False,
        new_unconditional_zero_proportion_proven=False, website_submission_ready=False)
    OUT.write_text(json.dumps(value, indent=2) + '\n', encoding='utf8')
    print(json.dumps(row(OUT)))


if __name__ == '__main__':
    main()
