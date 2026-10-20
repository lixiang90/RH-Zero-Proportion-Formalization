"""Prepare immutable submission text/metadata; zero proof or network execution."""
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
DRAFT = ROOT / 'research-goal-20261020-w9a2-delivery/draft-v5'
DEST = ROOT / 'submission/w9a2-weighted-potential-20261020-prepared'
SOURCE_SHA = '650ad1762ee36ba1ddf5f6a027900b20f0f85ba087ac099fd2c99a54eaf6ae13'
DRAFT_SHA = '497f905f1742380a38c8f5c93ac293d9a0d67717ea5e89e43067751631fe1527'
REVIEW = ROOT / 'research-goal-20261020-w9a2-verification-independent/formal-completion'
REVIEW_SHA = '2db147ef0e6d26efece5645544e385c7d7d4106145cea4c2a92581222c9cb90e'
ID = 'lixiang90-w9a2-weighted-potential-20261020'
SCORE = {'numerator': '3337881639516708570682858853672166187793',
         'denominator': '4955348542279967171490000000000000000000'}
METHOD = 'Exact weighted-potential transfer for the W9A2 nine-point Gram-defect certificate'
SUMMARY = ('Uses the attributed W9A2 nine-point Gram-defect certificate. A complete quantitative walk '
    'places every 17/20-separated real window in one of 24 retained leaves, in either orientation, or '
    'a good state. A 134-edge overlap graph and an exact rational potential improve the average '
    'energy floor. Telescoping pays one fixed boundary loss, charged once on the separated remainder '
    'in the matching partition. The actual zero-counting bridge then gives unconditional dyadic and '
    'cumulative bounds for distinct critical-line zeros at the stated exact p/q. All inherited '
    'source attributions and licenses are retained.')


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read(path):
    raw = path.read_bytes(); raw.decode('utf-8', errors='strict')
    return raw


def pin(path):
    raw = read(path)
    return {'path': path.relative_to(ROOT).as_posix(), 'bytes': len(raw), 'sha256': sha(raw)}


def write(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as stream:
        stream.write(raw)


def dump(obj):
    return (json.dumps(obj, ensure_ascii=False, indent=2) + '\n').encode()


def check_manifest(folder, expected):
    assert sha(read(folder / 'files.json')) == expected
    data = json.loads(read(folder / 'files.json'))
    for row in data['files']:
        raw = read(folder / row['path'])
        assert len(raw) == row['bytes'] and sha(raw) == row['sha256']
    return data


def main():
    assert not DEST.exists(), 'Never overwrite existing submission material'
    check_manifest(DRAFT, DRAFT_SHA)
    check_manifest(REVIEW, REVIEW_SHA)
    source = read(DRAFT / 'Solution.lean')
    assert len(source) == 1830001 and sha(source) == SOURCE_SHA
    assert len(SUMMARY) <= 1000 and len(SUMMARY.encode('utf-16-le')) // 2 <= 1000
    module_dir = DRAFT / 'frozen-inputs/StructuralW9A220261020'
    final, counting, graph = [read(module_dir / (name + '.lean')) for name in ['Final', 'Counting', 'Graph']]
    inputs = [DRAFT / 'files.json', DRAFT / 'Solution.lean', REVIEW / 'files.json', ROOT / 'LICENSE',
        ROOT / 'submission/single-exception-overlap-accepted-20261019/official/accepted-submission.json.body',
        ROOT / 'submission/single-exception-overlap-accepted-20261019/acceptance-status.json',
        *[module_dir / (name + '.lean') for name in ['Core', 'Graph', 'Localization', 'Counting', 'Final']]]
    before = [pin(p) for p in inputs]
    base = Fraction(893029029923108825, 10**20)
    mu = Fraction(622387738726, 5)
    increment = mu / 10**20
    boundary = Fraction(2504722000690, 5 * 10**20)
    pressure = Fraction(454741897490, 10**14)
    h = Fraction(6721237468782417141365717707344332375586, 10**40)
    c = base + increment
    exact = Fraction(int(SCORE['numerator']), int(SCORE['denominator']))
    assert (h - pressure) / (1 - c) == exact
    for literal in [b'893029029923108825 / 100000000000000000000',
        b'622387738726 / (5 * 100000000000000000000)',
        b'2504722000690 / (5 * 100000000000000000000)', b'454741897490 / 100000000000000']:
        assert literal in final
    assert b'6721237468782417141365717707344332375586' in counting
    assert b'abbrev State := Fin 49' in graph and b'Edge u v' in graph
    bad = re.search(rb'def badEdges[^\n]*:= (\[[^\n]+\])', graph)[1]
    assert len(re.findall(rb'\((\d+), (\d+)\)', bad)) == 37
    assert b'(622387738726 : \xe2\x84\xa4) + potential v - potential u \xe2\x89\xa4 5 * cost u' in graph
    receipts, roots = [], {}
    for version, module in [(0, 'Prefix'), (1, 'Core'), (3, 'Graph'), (4, 'Localization'), (4, 'Counting'), (5, 'Final')]:
        job = ROOT / f'tmp/w9a2-20261020/candidate-ordinary-v{version}'
        name = 'StructuralW9A220261020_' + module
        receipt_path = job / (name + '.receipt.json'); receipt = json.loads(read(receipt_path))
        log_path = job / (name + '.log'); log = read(log_path)
        assert receipt['ordinary_compile_passed'] is True and type(receipt['exit_code']) is int and receipt['exit_code'] == 0
        assert receipt['source_unchanged'] is True and sha(log) == receipt['log_sha256']
        assert all(set(axioms) <= {'propext', 'Quot.sound', 'Classical.choice'} for axioms in receipt['observed_axioms'].values())
        assert not set(roots).intersection(receipt['observed_axioms']); roots.update(receipt['observed_axioms'])
        receipts.append({'module': receipt['module'], 'development_stage': version,
            'source_sha256': receipt['source_sha256'], 'olean_sha256': receipt['olean_sha256'],
            'elapsed_seconds': receipt['elapsed_seconds'], 'receipt': pin(receipt_path), 'log': pin(log_path)})
        inputs += [receipt_path, log_path]
    assert len(roots) == 12
    # Preview the earlier accepted UI's trim policy without modifying/copying a
    # normalized candidate or claiming the current website uses the same policy.
    trim_chars = '\u0009\u000a\u000b\u000c\u000d\u0020\u00a0\u1680' + ''.join(chr(x) for x in range(0x2000, 0x200b)) + '\u2028\u2029\u202f\u205f\u3000\ufeff'
    trim_preview = source.decode().strip(trim_chars).encode()
    assert source == trim_preview + b'\n'
    prepared_at = datetime.now(timezone.utc).isoformat()
    proof = {'path': 'proof/Solution.lean', 'bytes': len(source), 'sha256': SOURCE_SHA,
             'copied_without_normalization': True, 'website_source_limit_bytes': 2000000, 'source_slack_bytes': 169999}
    submission = {'schemaVersion': 1, 'id': ID, 'track': 'critical-line',
        'author': {'github': 'lixiang90', 'displayName': 'Li Xiang'}, 'score': SCORE,
        'proof': {'solution': 'proof/Solution.lean', 'theorem': 'candidate_critical_line_bound',
            'cumulativeTheorem': 'candidate_critical_line_bound_cumulative', 'improvementTheorem': 'candidate_strict_improvement'},
        'summary': SUMMARY, 'method': METHOD, 'model': '', 'harness': 'Codex', 'license': 'Apache-2.0'}
    fields = {'schema': 'reviewable-website-form-fields-prepared-v1', 'proposed_id': ID,
        'suggested_result_name': ID, 'public_display_name': 'Li Xiang', 'authenticated_GitHub_login': 'lixiang90',
        'identity_source': 'User authorized name and parent root reported current authenticated GitHub identity',
        'method': METHOD, 'score': SCORE, 'summary': SUMMARY,
        'summary_characters': len(SUMMARY), 'summary_utf16_code_units': len(SUMMARY.encode('utf-16-le')) // 2,
        'coding_harness_optional': 'Codex', 'AI_model_optional': None, 'model_field_value': '',
        'model_status': 'Exact current model identifier not independently verified; leave optional field blank',
        'proof_file': proof, 'upload_ready': False, 'submitted': False, 'official_website_acceptance': False}
    status = {'schema': 'w9a2-prepared-verification-status-v1', 'prepared_at_utc': prepared_at,
        'source': proof, 'ordinary_modular_complete_actual_Lean_passed': True,
        'ordinary_scope': 'Explicit development stages with exact passing Prefix/Core/Graph/Localization/Counting/Final; not one fresh single-file run',
        'ordinary_printed_root_count': 12, 'ordinary_printed_axioms': roots,
        'allowed_axioms': ['propext', 'Quot.sound', 'Classical.choice'],
        'old_failed_Final_sorryAx_placeholders_rejected': True,
        'single_file_ordinary_compile_passed': False, 'Comparator_statement_dependency_primitive_passed': False,
        'Comparator_transitive_axioms_passed': False, 'default_Lean_kernel_replay_passed': False,
        'independent_serial_nanoda_passed': False, 'complete_single_3200s_production_passed': False,
        'official_website_acceptance_confirmed': False, 'upload_ready': False, 'submitted': False,
        'public_job_id': None, 'public_acceptance_commit': None,
        'future_production_results_must_be_separate_hash_linked_addendum': True,
        'never_edit_frozen_Solution_bytes': True, 'proof_export_kernel_calls_by_material_preparer': 0}
    provenance = {'schema': 'w9a2-prepared-material-source-provenance-v1', 'prepared_at_utc': prepared_at,
        'source_origin': pin(DRAFT / 'Solution.lean'), 'source_draft_manifest': pin(DRAFT / 'files.json'),
        'source_copied_without_normalization': True, 'all_embedded_notices_attributions_licenses_retained': True,
        'original_accepted_metadata_format_reference': pin(inputs[4]),
        'root_project_license_copied_verbatim': pin(ROOT / 'LICENSE'),
        'source_is_complete_single_file_with_all_five_candidate_modules': True,
        'official_record_or_upload_claimed': False, 'old_materials_modified': False,
        'model_identifier_not_guessed': True, 'proof_export_kernel_network_calls': 0}
    formulas = {'scope': 'Exact source literal and rational metadata checks, not a new proof/kernel run',
        'module_sources': [pin(module_dir / (name + '.lean')) for name in ['Core', 'Graph', 'Localization', 'Counting', 'Final']],
        'base': str(base), 'mu_integer_cost_units': str(mu), 'increment': str(increment), 'c': str(c),
        'boundary_C': str(boundary), 'pressure_B': str(pressure), 'H': str(h), 'kappa': str(exact),
        'exceptional_cells': 24, 'oriented_exceptional_states': 48, 'good_states': 1,
        'leaf_to_leaf_edges': 37, 'good_related_edges': 97, 'total_edges': 134,
        'strict_shared_span_exclusions': 2267, 'potential_min': '0', 'potential_max_integer': '2504722000690',
        'integer_edge_certificate': '622387738726 + potential(v) - potential(u) <= 5 * cost(u)',
        'summed_energy': 'c*N - C <= sum E_i',
        'finite_matching_bound_n9': '(c-32*delta)*m - B*R - 8*c - C <= defect',
        'effective_counting_boundary_parameter': 10,
        'exact_ratio_identity_checked_with_Fraction': True, 'global_optimality_claimed': False}
    references = {'schema': 'w9a2-prepared-evidence-references-v1',
        'formal_completion_independent_manifest': pin(REVIEW / 'files.json'), 'actual_modular_receipts': receipts,
        'three_public_roots': ['candidate_strict_improvement', 'candidate_critical_line_bound', 'candidate_critical_line_bound_cumulative'],
        'fullrunner_frozen': pin(ROOT / 'research-goal-20261020-w9a2-verification-preparation-v1/run_verification.py'),
        'fullrunner_prepared_manifest': pin(ROOT / 'research-goal-20261020-w9a2-verification-preparation-v1/prepared-files.json'),
        'fresh_record_receipt': None, 'actual_complete_production_receipt': None, 'official_acceptance_receipt': None}
    normalization = {'scope': 'Historical-UI trim preview only; no source bytes changed and no current policy asserted',
        'historical_policy_reference': pin(inputs[5]), 'immutable_local_source': proof,
        'if_current_UI_applies_same_ECMAScript_trim': {'bytes': len(trim_preview), 'sha256': sha(trim_preview), 'removed_bytes': 1},
        'current_UI_policy_and_remote_accepted_source_must_be_observed_by_root': True,
        'normalized_candidate_file_written': False}
    DEST.mkdir(parents=True, exist_ok=False)
    write(DEST / 'proof/Solution.lean', source)
    write(DEST / 'proof/Solution.manifest.json', dump(proof))
    for name, obj in [('submission.draft.json', submission), ('website-fields.draft.json', fields),
        ('verification-status.json', status), ('provenance.json', provenance),
        ('mathematical-source-check.json', formulas), ('evidence-references.json', references),
        ('UI-normalization-preview.json', normalization)]:
        write(DEST / name, dump(obj))
    write(DEST / 'LICENSE', read(ROOT / 'LICENSE'))
    # Frozen prose is maintained next to this generator; copy exactly once.
    for name in ['README.zh.md', 'MATHEMATICS.zh.md', 'ATTRIBUTION.zh.md']:
        write(DEST / name, read(HERE / name))
    assert read(DEST / 'proof/Solution.lean') == source
    assert before == [pin(p) for p in inputs[:len(before)]]
    check_manifest(DRAFT, DRAFT_SHA); check_manifest(REVIEW, REVIEW_SHA)
    files = [{'path': p.relative_to(DEST).as_posix(), 'bytes': p.stat().st_size, 'sha256': sha(read(p))}
             for p in sorted(DEST.rglob('*')) if p.is_file()]
    write(DEST / 'files.json', dump({'schema': 'w9a2-submission-prepared-materials-manifest-v1',
        'scope': 'Prepared immutable source and submission fields; modular ordinary math only, production/official pending',
        'upload_ready': False, 'source_sha256': SOURCE_SHA, 'files': files}))
    print(json.dumps({'prepared_directory': str(DEST.relative_to(ROOT)), 'source_bytes': len(source),
        'source_sha256': SOURCE_SHA, 'manifest_sha256': sha(read(DEST / 'files.json')),
        'summary_characters': len(SUMMARY), 'upload_ready': False, 'proof_export_kernel_network_calls': 0}))


if __name__ == '__main__':
    main()
