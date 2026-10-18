"""Metadata-only static-plan freezer. Does not import/run any verifier or binary."""
from pathlib import Path
import hashlib
import json
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(__file__).resolve().parent

def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda: f.read(1048576), b''):
            h.update(chunk)
    return h.hexdigest()

def read(rel):
    return json.loads((ROOT / rel).read_text(encoding='utf8'))

def write(name, obj):
    p = OUT / name
    assert not p.exists(), str(p)
    p.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + '\n', encoding='utf8', newline='\n')

def bind(rel):
    p = ROOT / rel
    return {'path': rel, 'bytes': p.stat().st_size, 'sha256': sha(p)}

runtime = read('tmp/setup-20261015/runtime.json')
nano = read('verification/gram-defect-20261015/setup/nanoda-build.json')
old = read('verification/gram-defect-20261015/lean/single/verification.json')
policy = read('research-goal-20261017-w10-generator-policy/policy-snapshot.json')
deps = [
    'scripts/verify_record_20261015.py', 'scripts/verify_single_solution.py',
    'tools/ComparatorCoreAudit.lean', 'tmp/setup-20261015/runtime.json',
    'tmp/setup-20261015/sources.json', 'lake-manifest.json',
    'verification/gram-defect-20261015/setup/nanoda-build.json',
    'verification/gram-defect-20261015/lean/single/verification.json',
    'tmp/setup-20261015/packages/Zeta23/comparator/ChallengeDeps.lean',
    'research-goal-20261017-w10-generator-policy/policy-snapshot.json',
    'research-goal-20261017-w10-generator-policy/snapshot/challenge/contract.json',
    'research-goal-20261017-w10-generator-policy/snapshot/CONTRIBUTING.md',
    'research-goal-20261017-w10-generator-policy/snapshot/scripts/prepare-candidate.ts',
    'research-goal-20261017-w10-generator-policy/snapshot/scripts/verify-submission.ts',
    'research-goal-20261017-w10-generator-policy/snapshot/scripts/run-comparator-e2b.sh',
    'research-goal-20261017-w10-generator-policy/snapshot/e2b/run-verification-job.sh',
    'research-20261016-w10-cert/website-snapshot/provenance.json',
    'research-20261016-w10-cert/website-snapshot/challenge/templates/CandidateSpec.lean.tmpl',
    'research-20261016-w10-cert/website-snapshot/challenge/templates/Challenge.Candidate.lean',
    'research-goal-20261018-tiny-flatten-preparation/prepared-files.json',
    'research-goal-20261018-tiny-flatten-preparation/generate_draft.py',
    'research-goal-20261018-tiny-flatten-preparation/candidate-parameters.json',
    'research-goal-20261018-tiny-flatten-preparation/SPEC.zh.md',
    'research-goal-20261018-tiny-dev-static-review/files.json',
    'research-goal-20261018-tiny-runtime-preparation/compiler-prepared.json',
]
before = [bind(rel) for rel in deps]
keys = ['ordinary_single_file_lean_passed', 'statement_equality_proved',
        'permitted_axioms_checked', 'default_kernel_replay_passed',
        'independent_nanoda_passed', 'local_single_file_verified',
        'official_website_acceptance', 'checked_declarations']
provenance = {
    'schema': 'tiny-static-production-provenance-v1',
    'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
    'scope': 'Metadata-only inspection of existing recipes and receipts; no new verification run',
    'runtime': {k: runtime[k] for k in ['lean', 'lean_sha256', 'lean_version',
                                      'compiler_archive_sha256', 'package_root', 'lean_path']},
    'pinned_archives': [x for x in runtime['source_archives']
                        if x['name'] in ['Zeta23', 'mathlib', 'Comparator', 'lean4export', 'nanoda']],
    'nanoda_build_receipt': nano,
    'prior_candidate_only': {
        'receipt': 'verification/gram-defect-20261015/lean/single/verification.json',
        'results': {k: old.get(k) for k in keys},
        'actual_pipeline': 'scripts/verify_record_20261015.py adapts verify_single_solution.py from pinned archives',
        'user_oleans_may_be_reused_for_tiny': False,
        'tiny_result_inferred': False,
    },
    'official_capture_commit': policy['commit'],
    'generator_executed': False,
    'lean_export_comparator_nanoda_executed': False,
    'new_network_request': False,
    'new_trusted_spec_written': False,
    'new_runner_implemented': False,
    'total_3200s_proven': False,
    'official_acceptance': False,
    'bound_dependencies': before,
}
assert before == [bind(rel) for rel in deps], 'Dependency changed during static reading'
write('tool-provenance.json', provenance)
files = [bind(str(p.relative_to(ROOT)).replace('\\', '/'))
         for p in sorted(OUT.iterdir()) if p.is_file()]
write('files.json', {'schema': 'static-production-plan-files-v1',
                     'scope': 'Static plan and command text only; execution gates remain open',
                     'files': files, 'dependencies': before,
                     'all_dependency_bytes_unchanged': True})
print(json.dumps({'manifest': str((OUT / 'files.json').relative_to(ROOT)),
                  'sha256': sha(OUT / 'files.json'), 'files': len(files),
                  'no_verifier_execution': True}))
