"""Freeze a read-only source review; no Lean, optimizer or mathematical replay."""
from pathlib import Path
import hashlib, json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

def record(p):
    raw = p.read_bytes()
    return {"path": p.relative_to(ROOT).as_posix(), "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest()}

deps = [
    'StructuralW10Cert20261016/CompressedCommands.lean',
    'research-20261016-w10-cert/compressed-commands-verification.json',
    'research-20261016-w10-cert/compressed-preflight.json',
    'research-20261016-w10-cert/compressed-preflight-resources.log',
    'research-20261016-w10-cert/generate.py',
    'research-20261016-w10-cert/ordered_generate.py',
    'research-20261016-w10-cert/compact_thin.py',
    'research-20261016-w10-cert/relative_codec.py',
    'research-20261016-w10-cert/tree_flow.py',
    'research-goal-20261016/w10-cell-predictor-20261017/NOTE.md',
    'research-goal-20261016/w10-size-audit-20261017/field-huffman.json',
    'research-goal-20261016/lean_leaf_batch_benchmark_receipt.json',
    'research-goal-20261016/lean_aux478_proof_index.json',
    'research-goal-20261017-w10-generator-policy/policy-snapshot.json',
    'research-goal-20261017-w10-generator-policy/snapshot/CONTRIBUTING.md',
    'research-goal-20261017-w10-generator-policy/snapshot/SECURITY.md',
    'research-goal-20261017-w10-generator-policy/snapshot/scripts/prepare-candidate.ts',
    'research-goal-20261017-w10-generator-policy/snapshot/scripts/run-comparator-e2b.sh',
    'research-goal-20261017-w10-generator-policy/snapshot/e2b/run-verification-job.sh',
    'tmp/setup-20261015/packages/Comparator/Main.lean',
]
mathroot = 'tmp/setup-20261015/packages/mathlib/'
mathpaths = [
    'Mathlib/Tactic/Linarith/Oracle/SimplexAlgorithm.lean',
    'Mathlib/Tactic/Linarith/Oracle/SimplexAlgorithm/PositiveVector.lean',
    'Mathlib/Tactic/Linarith/Oracle/SimplexAlgorithm/SimplexAlgorithm.lean',
    'Mathlib/Tactic/Linarith/Oracle/SimplexAlgorithm/Gauss.lean',
    'Mathlib/Tactic/Linarith/Oracle/SimplexAlgorithm/Datatypes.lean',
]
report = {
    'scope': 'Static source/policy/API review only; no candidate implementation or execution.',
    'files': [record(HERE / 'REPORT.zh.txt'), record(Path(__file__))],
    'dependencies': [record(ROOT / n) for n in deps],
    'runtime_dependency_not_staged_wholesale': [
        {**record(ROOT / (mathroot + n)),
         'source_url': 'https://github.com/leanprover-community/mathlib4/blob/'
                       '51e6992efd06126df61a496bebf8f49482a4e129/' + n}
        for n in mathpaths
    ],
    'new_Lean_files': 0, 'Lean_invocations': 0, 'solver_calls': 0,
    'prototype_implemented': False, 'whole_tree_reconstruction_proven': False,
    'website_source_size_passed': False, 'website_runtime_passed': False,
    'complete_global_floor_proven': False, 'new_zero_proportion_proven': False,
    'recommendation': 'Pause implementation; payload-only feasibility does not resolve kernel resource gate.',
}
target = HERE / 'review-files.json'
with target.open('x', encoding='utf-8', newline='\n') as f:
    json.dump(report, f, ensure_ascii=False, indent=2)
    f.write('\n')
print(json.dumps({'manifest': target.relative_to(ROOT).as_posix(),
                  'sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
                  'owned_files': len(report['files']),
                  'owned_bytes': sum(x['bytes'] for x in report['files'])}))
