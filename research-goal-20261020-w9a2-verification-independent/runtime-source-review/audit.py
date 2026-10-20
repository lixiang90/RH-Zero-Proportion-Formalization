"""Read files/AST/hash only. Never imports or runs the runtime assembler."""
import ast
import difflib
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
PACKAGE = ROOT / 'research-goal-20261020-w9a2-runtime-closure-v1'
SEEN = {}


def sha(raw): return hashlib.sha256(raw).hexdigest()


def read(path):
    raw = path.read_bytes()
    key = path.resolve().relative_to(ROOT.resolve()).as_posix()
    row = {'bytes': len(raw), 'sha256': sha(raw)}
    assert SEEN.setdefault(key, row) == row, key
    return raw


def main():
    path = PACKAGE / 'prepared-files.json'
    manifest = read(path)
    assert sha(manifest) == '6c22815d8d200bca43e92886a926daf1ecdb3d6840f0080a7bd85179dbfe72f7'
    rows = json.loads(manifest)['files']
    assert len(rows) == len({r['path'] for r in rows})
    for row in rows:
        p = (PACKAGE / row['path']).resolve()
        assert p.is_relative_to(PACKAGE.resolve())
        raw = read(p)
        assert len(raw) == row['bytes'] and sha(raw) == row['sha256']
    assembler = read(PACKAGE / 'assemble.py')
    helper = read(PACKAGE / 'cache_binding.py')
    assert sha(assembler) == '550762bc42b133ae6290407526b4bce2d54cd71d432a06ea2038965ebf997aa9'
    assert sha(helper) == '76d5d5add51c61bfa21a7d51bb4ef912dbe1e95a6eac681cc239ffd947c9cd62'
    ast.parse(assembler); ast.parse(helper)
    assert b'if not __debug__:' in assembler
    for name in ['assemble.py', 'cache_binding.py']:
        old = read(PACKAGE / 'archive-pre-review-v0' / name).decode()
        new = read(PACKAGE / name).decode()
        diff = ''.join(difflib.unified_diff(old.splitlines(keepends=True),new.splitlines(keepends=True),
            fromfile='archive-pre-review-v0/' + name,tofile='revision2/' + name))
        with (HERE / (name + '.diff')).open('xb') as stream: stream.write(diff.encode())
    for rel in ['tmp/lean-toolchain/include/lean/lean.h',
        'tmp/lean-toolchain/src/lean/Init/Data/Hashable.lean',
        'tmp/lean-toolchain/src/lean/Init/Prelude.lean',
        'tmp/lean-toolchain/src/lean/lake/Lake/Build/Trace.lean',
        'tmp/lean-toolchain/src/lean/lake/Lake/Build/Module.lean',
        'tmp/lean-toolchain/src/lean/Lean/Elab/ParseImportsFast.lean',
        '.lake/packages/mathlib/Cache/Hashing.lean','.lake/packages/mathlib/Cache/IO.lean',
        'verification/comparator-core-public-driver-check.json',
        'verification/three-website-declarations-modular-nanoda.json',
        'verification/gram-defect-single-20261014/independent-kernel.json']:
        read(ROOT / rel)
    before = dict(SEEN)
    for key in list(before): read(ROOT / key)
    report = {'scope': 'Independent static source/ABI/provenance-bridge review only',
        'status': 'PASS_STATIC_EXECUTION_STILL_REQUIRED',
        'manifest_sha256': sha(manifest), 'manifest_rows': len(rows), 'input_count': len(before),
        'input_before_after_identical': True, 'inputs': before,
        'assembler_sha256': sha(assembler), 'helper_sha256': sha(helper),
        'verified_statically': ['Borrowed string and byte-array ABI corresponds to current x64 SDK lean.h',
            'Mix/list/UInt64/Lake1723/cache-generation5/source-path/import-order formulas correspond to current sources',
            'Official archive/member comparison precedes SDKHash DLL load and only two borrowed hash APIs operate on caller-owned buffers',
            'Dictionary output traversal, bytewise CRLF normalization and atomic public-section import-header rollback are present',
            'Legacy Zeta source/options/package/module/import-artifact/recursive depHash inputs and actual data hashes checked by algorithm',
            'Nested parser and four Comparator oleans reuse exact historical hashes with same SDK, fixed source commits and raw/LF source bridge',
            'Native exporter and Nano use exact historical binary hashes and retained source/build provenance',
            'Tracked package root configurations are canonical Git blobs and Python optimization cannot bypass asserts',
            'PE application closure includes observed Python native extensions and Lean paths with an explicit System32/API-set boundary',
            'Clean overlays exclude cached candidate user modules; actual terminal exit0 and root approval remain required'],
        'remaining_known_deterministic_code_blockers': [],
        'actual_DLL_hash_API_calls_by_reviewer': 0, 'assembler_runs_by_reviewer': 0,
        'compiler_export_kernel_runs_by_reviewer': 0, 'round_counter_changes': 0,
        'actual_runtime_closure_verified_by_this_report': False,
        'actual_source_cache_hash_control_pass_proven_by_this_report': False,
        'candidate_proof_acceptance_proven_by_this_report': False}
    with (HERE / 'review.json').open('x',encoding='utf-8',newline='\n') as stream:
        json.dump(report,stream,ensure_ascii=False,indent=2); stream.write('\n')
    print(json.dumps({k: report[k] for k in ['status','manifest_rows','input_count','assembler_sha256','helper_sha256','assembler_runs_by_reviewer']}))


if __name__ == '__main__': main()
