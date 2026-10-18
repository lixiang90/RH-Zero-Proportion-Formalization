"""Read-only byte, statement and exact score review of accepted-v3 materials.

No builder/producer imports, network, compiler, kernel, collector or search.
"""
from fractions import Fraction as F
import hashlib
import json
import os
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
MAT = ROOT / 'submission/single-exception-overlap-accepted-20261019'
OFF = ROOT / 'research-goal-20261019-record-accepted-independent-1753'
OLD = ROOT / 'research-goal-20261018-tiny-flatten-preparation-v3/draft/Solution.lean'
PIN = '11483f1e7214104d842cab76137a11fd22210c7b00a0013e8279414008bc49fd'
OFF_PIN = 'c528b3b8a5646fe36d924721c5a61ee3193382764dd98cdfa58932f3b2e4b652'
SRC = '024902a7ef01ccba2a6c71e54682a31712417e5d3c0b4ead5f6f80ad25fd1a81'
DIGEST = '23e3dd765aa27de76938e056f13d3e0f08d849d0e7c39c6f78c62e7640c0a10f'


def sha(b):
    return hashlib.sha256(b).hexdigest()


def read_json(p):
    return json.loads(p.read_bytes())


def file_row(p, base=ROOT):
    data = p.read_bytes()
    return {'path': p.relative_to(base).as_posix(), 'bytes': len(data), 'sha256': sha(data)}


def write_new(p, data):
    with p.open('x', encoding='utf-8', newline='\n') as out:
        json.dump(data, out, ensure_ascii=False, indent=2)
        out.write('\n')
        out.flush()
        os.fsync(out.fileno())


def main():
    assert __debug__
    receipt = HERE / 'independent-review.json'
    assert not receipt.exists(), 'One immutable review only'
    material_manifest = MAT / 'files.json'
    official_manifest = OFF / 'accepted-files.json'
    assert sha(material_manifest.read_bytes()) == PIN
    assert sha(official_manifest.read_bytes()) == OFF_PIN
    materials = read_json(material_manifest)
    official = read_json(official_manifest)
    checked = [material_manifest, official_manifest, OLD]
    internal_names = set()
    for item in materials['files']:
        assert item['path'] not in internal_names
        internal_names.add(item['path'])
        p = MAT / item['path']
        assert p.resolve().is_relative_to(MAT.resolve())
        assert file_row(p, MAT) == item
        checked.append(p)
    actual_names = {p.relative_to(MAT).as_posix() for p in MAT.rglob('*') if p.is_file()}
    assert actual_names == internal_names | {'files.json'}
    for item in official['files'] + official['read_dependencies']:
        p = ROOT / item['path']
        assert file_row(p) == {key: item[key] for key in ['path', 'bytes', 'sha256']}
        checked.append(p)
    before = {str(p): sha(p.read_bytes()) for p in checked}

    source = (MAT / 'proof/Solution.lean').read_bytes()
    assert source == (OFF / 'accepted-Solution.lean.body').read_bytes() == OLD.read_bytes()
    assert len(source) == 1979280 <= 2000000 and sha(source) == SRC
    submitted_manifest = (MAT / 'official/accepted-submission.json.body').read_bytes()
    assert submitted_manifest == (OFF / 'accepted-submission.json.body').read_bytes()
    assert len(submitted_manifest) == 1533
    assert sha(b'submission.json\0' + submitted_manifest + b'proof/Solution.lean\0' + source) == DIGEST
    for name in ['comparison.json', 'leaderboard.body', 'leaderboard.http.json',
                 'accepted-submission.json.http.json', 'accepted-Solution.lean.http.json', 'files.json']:
        assert (MAT / 'official' / name).read_bytes() == (OFF / name).read_bytes()

    status = read_json(MAT / 'acceptance-status.json')
    publication = json.loads(submitted_manifest)
    comparison = read_json(MAT / 'official/comparison.json')
    record = comparison['current_public_record']
    improvement = read_json(MAT / 'strict-improvement.json')
    expected_id = 'lixiang90-single-exception-overlap-20261018'
    assert record['id'] == publication['id'] == status['record_id'] == expected_id
    assert record['author'] == status['author'] == 'Li Xiang'
    assert record['github'] == status['github'] == 'lixiang90'
    assert publication['author'] == {'github': 'lixiang90', 'displayName': 'Li Xiang'}
    assert record['status'] == status['status'] == 'kernel-verified'
    assert record['formalVerification'] is True and status['formalVerification'] is True
    assert status['official_website_acceptance_confirmed'] is True
    assert record['exactRational'] == status['score'] == publication['score']
    assert status['public_elapsed_seconds'] is None
    assert status['official_fixed_policy_verified'] is True
    assert status['source_limit_bytes'] == 2000000 and status['fixed_pipeline_budget_seconds'] == 3200
    assert status['current_R_equals_candidate_because_this_submission_promoted'] is True
    assert status['do_not_require_improvement_over_own_promoted_kappa'] is True

    candidate = F(improvement['candidate'])
    baseline = F(improvement['previous_record'])
    assert candidate == F(int(record['exactRational']['numerator']), int(record['exactRational']['denominator']))
    assert candidate - baseline == F(improvement['exact_gain']) > 0
    assert baseline == F(3337839448633819172184136761695440236797,
                         4955319193847235264050000000000000000000)
    c = F(893616123055294719 + 389500523, 10**20)
    H = F(6721290091768038344368273523390880473594, 10**40)
    B = F(456111945004000000, 10**20)
    assert (H - B) / (1 - c) == candidate

    text = source.decode('utf-8')
    expected_statements = {
        'candidate_strict_improvement': 'currentRecordKappa < candidateKappa',
        'candidate_critical_line_bound': '∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (candidateKappa - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T)',
        'candidate_critical_line_bound_cumulative': '∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (candidateKappa - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T',
    }
    statements = {}
    for name, wanted in expected_statements.items():
        found = re.findall(r'^theorem ' + name + r'\s*:\s*(.*?)\s*:= by', text, re.M | re.S)
        assert len(found) == 1
        statement = re.sub(r'\s+', ' ', found[0]).strip()
        assert statement == wanted
        statements[name] = statement
    assert re.search(r'^import ChallengeDeps\.CandidateSpec$', text, re.M)
    assert not re.search(r'^(?:private )?(?:def|abbrev|axiom) (?:candidateKappa|currentRecordKappa)\b', text, re.M)
    assert '_root_.Ncount T (2*T)' in text and '_root_.N0star T (2*T)' in text
    assert '_root_.Ncount 0 T' in text and '_root_.N0star 0 T' in text
    assert 'exact StructuralS1RTiny20261018.Dev.Final.actual_dyadic' in text
    assert 'exact StructuralS1RTiny20261018.Dev.Final.actual_cumulative' in text

    math = (MAT / 'MATHEMATICS.zh.md').read_text(encoding='utf-8')
    readme = (MAT / 'README.zh.md').read_text(encoding='utf-8')
    for phrase in ['九个点、八个相邻gap', '同一十点、九gap', '四种独立反射',
                   '不是仅保留全局极小点或KKT点', '没有Riemann假设', 'Σᵢ Eᵢ ≥ c·n − δ']:
        assert phrase in math
    assert 'pending' in publication['summary']
    assert '上传当时的pending句子不代表当前状态' in readme
    assert '不回写为本地统一PASS' in readme
    assert '公开record/submission未披露实际耗时' in readme
    historical = read_json(MAT / 'official/local-kernel-checks-historical.json')
    assert historical['full_cold3200s_passed'] is False
    assert historical['independent_complete_nanoda_passed'] is True
    assert historical['nanoda_declarations'] == 75371
    assert historical['nanoda_seconds'] == 427.389541876
    # A frozen source/preparation comment and public upload summary can retain
    # their historical DRAFT/pending wording. The accepted API controls status.
    assert 'DRAFT, upload_ready=false' in text

    cancelled = ROOT / 'research-goal-20261019-native-v4-superseded/status.json'
    cancellation_manifest = cancelled.parent / 'files.json'
    assert sha(cancellation_manifest.read_bytes()) == '741e0325ba42ef89ee89ef9267c415fd77bbed693498c63ed17f8c88a99a2545'
    cancellation = read_json(cancelled)
    assert cancellation['status'] == 'cancelled_as_redundant_after_authoritative_v3_acceptance'
    assert cancellation['full_local_verification_PASS'] is False
    assert cancellation['mathematical_counterexample_or_refutation'] is False
    final_flat = ROOT / 'research-goal-20261019-final-accepted-delivery/files.json'
    final_flat_pin = 'd3a0f4fcc35af837dc722eb60a928375caa8de11f5034ae0b8d11ecdedf57e63'
    assert sha(final_flat.read_bytes()) == final_flat_pin
    checked += [cancelled, cancellation_manifest, final_flat]
    assert before == {p: sha(Path(p).read_bytes()) for p in before}
    report = {
        'schema': 'independent-final-accepted-v3-materials-review-v1', 'passed': True,
        'materials_manifest_sha256': PIN, 'official_accepted_manifest_sha256': OFF_PIN,
        'internal_rows_checked': len(materials['files']), 'internal_file_set_complete': True,
        'source_bytes': len(source), 'source_sha256': SRC, 'source_within_2MB': True,
        'official_raw_equals_archived_and_original_uploaded_v3': True,
        'canonical_submission_plus_proof_digest': DIGEST, 'digest_matches_user_job': True,
        'official_record_id': expected_id, 'official_status': 'kernel-verified',
        'formalVerification': True, 'public_elapsed_seconds': None,
        'official_fixed_pipeline_acceptance_is_authoritative_policy_evidence': True,
        'local_total3200_failure_and_separate_nanoda_PASS_preserved_as_history': True,
        'candidate': str(candidate), 'historical_baseline': str(baseline),
        'exact_strict_gain': str(candidate-baseline), 'ratio_H_B_c_exact': True,
        'current_record_equality_is_this_submission_promotion': True,
        'public_theorem_statements': statements,
        'wrapper_has_only_epsilon_and_eventually_large_height_quantifiers': True,
        'actual_root_Ncount_N0star_referenced': True,
        'no_trusted_candidate_or_record_constant_redefinition_detected': True,
        'nine_point_eight_gap_mathematics_and_global_exception_scope_reviewed': True,
        'historical_public_summary_and_source_DRAFT_preserved_not_current_status': True,
        'nonblocking_stale_material_wording': ['README says native-v4 is running; it was separately cancelled. This review records the actual cancellation without changing frozen materials.'],
        'native_v4_actual_current_status': cancellation['status'],
        'native_v4_neither_full_PASS_nor_mathematical_refutation': True,
        'final_flat_manifest': {'path': final_flat.relative_to(ROOT).as_posix(),
                                'sha256': final_flat_pin, 'scope': 'Manifest identity checked; all-flat cloud audit remains root-owned'},
        'final_project_cloud_sync': 'Pending root final byte audit; not independently claimed here',
        'producer_or_builder_imports': 0, 'network_compiler_kernel_collector_runs': 0,
        'mathematical_proof_recompilation': False,
        'inputs_sha256_start_end_equal': True,
        'read_dependencies': [file_row(p) for p in sorted(set(checked))],
    }
    write_new(receipt, report)
    print(json.dumps({'passed': True, 'receipt_sha256': sha(receipt.read_bytes()),
                      'source_sha256': SRC, 'internal_rows': len(materials['files'])}))


if __name__ == '__main__':
    main()
