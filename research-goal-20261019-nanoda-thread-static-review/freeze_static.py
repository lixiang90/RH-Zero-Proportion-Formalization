"""Metadata-only static source pinning; no verifier execution."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

def row(name):
    b = (ROOT / name).read_bytes()
    return {'path': name, 'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()}

def main():
    names = [
        'tmp/setup-20261015/packages/nanoda/src/tc.rs',
        'tmp/setup-20261015/packages/nanoda/src/util.rs',
        'tmp/setup-20261015/packages/nanoda/src/main.rs',
        'tmp/setup-20261015/packages/nanoda/src/lib.rs',
        'tmp/setup-20261015/packages/nanoda/src/parser.rs',
        'tmp/setup-20261015/packages/Comparator/Main.lean',
        'research-goal-20261017-w10-generator-policy/snapshot/challenge/contract.json',
        'research-goal-20261018-tiny-production-preparation/run_production.py',
        'tmp/current-s1r-tiny-20261018/production-v0/failure.json',
        'verification/gram-defect-20261015/setup/nanoda-build.json',
    ]
    before = [row(n) for n in names]
    result = {'schema': 'nanoda-thread-static-review-v1',
        'files': [row(p.relative_to(ROOT).as_posix()) for p in sorted(HERE.iterdir()) if p.is_file()],
        'dependencies': before, 'threads_config_changed': False,
        'verifier_runs': 0, 'benchmark_runs': 0, 'network_requests': 0,
        'locked_official_Comparator_omits_num_threads': True,
        'nanoda_serde_default_num_threads': 0,
        'locked_official_default_checking_is_serial': True,
        'more_threads_alone_do_not_reduce_proof_checking_scope': True,
        'local_runtime_not_equated_with_official_runtime': True}
    assert before == [row(n) for n in names]
    p = HERE / 'files.json'
    with p.open('x', encoding='utf-8', newline='\n') as f:
        json.dump(result, f, ensure_ascii=False, indent=2); f.write('\n')
    print(hashlib.sha256(p.read_bytes()).hexdigest())

if __name__ == '__main__':
    main()
