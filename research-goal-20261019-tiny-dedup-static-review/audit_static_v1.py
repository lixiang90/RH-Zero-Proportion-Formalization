"""Read-only source/byte feasibility audit. Never emits or compiles a Lean source.

Only JSON metadata and a human-readable report are written. Hypothetical byte
counts are sums over retained segments, not a generated production candidate.
"""
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PINS = {
    'StructuralS1RTiny20261018/Core.lean': '9fbdf3f2dc62333b636d3b25dfb3bf2b15e3b8c628ece73d6ba1bc768fc5f1a6',
    'StructuralS1RM20261018/CurrentPrefix.lean': 'ea8e01118d19158ba8313504910645ad467ea86eb2ea65a897859ae98101df21',
    'StructuralS1RTiny20261018/Dev/Core.lean': '1e144c848b39c85277af45c590cb0e54e93b2f098d44f5eb40bcb2e1b8d216ac',
    'StructuralS1RTiny20261018/Phase1/Localization.lean': 'ad722eca53b43ff28ccfe9f66e338979ac05ff7088fe067dc395ea5e1c9cf758',
    'StructuralS1RTiny20261018/Phase2/Counting.lean': '2bda5c9df708b4568f8f08447894cb73a3c6ecb9d2c77be67e2eb46387be868e',
    'StructuralS1RTiny20261018/Phase4/Final.lean': 'd477fd3181e0d4d5a3c89bcbcb987dd6cad00fbdde1946d01c26ac0c279489ed',
    'research-goal-20261018-tiny-flatten-preparation-v3/prepared-files.json': '8d866f77503210091280574f6a14fcead5461f07c156f383f1b67f78ee52ab32',
    'research-goal-20261018-tiny-production-preparation/prepared-files.json': '8de6adf94411254d8aef96e625faa1dc869069848049e99eab31e38a06e957c1',
}
EXTRA = [
    'research-goal-20261018-tiny-flatten-preparation-v3/generate_draft.py',
    'research-goal-20261018-tiny-flatten-preparation-v3/official-wrapper.lean.txt',
    'research-goal-20261018-tiny-flatten-preparation-v3/preparation.json',
    'research-goal-20261018-tiny-runtime-preparation/prepare_dev_sources.py',
    'research-goal-20261018-tiny-runtime-preparation/dev-source-files.json',
    'tmp/setup-20261015/packages/lean4export/Export.lean',
    'tmp/setup-20261015/packages/lean4export/Main.lean',
]

def sha(b):
    return hashlib.sha256(b).hexdigest()

def row(name):
    data = (ROOT / name).read_bytes()
    return {'path': name, 'bytes': len(data), 'sha256': sha(data)}

def write(name, obj):
    with (HERE / name).open('x', encoding='utf-8', newline='\n') as f:
        json.dump(obj, f, ensure_ascii=False, indent=2); f.write('\n')

def byte_count(text):
    return len(text.encode('utf-8'))

def main():
    before = [row(n) for n in list(PINS) + EXTRA]
    for r in before:
        if r['path'] in PINS:
            assert r['sha256'] == PINS[r['path']], r['path']
    s = (ROOT / 'StructuralS1RTiny20261018/Core.lean').read_text(encoding='utf-8')
    d = (ROOT / 'StructuralS1RTiny20261018/Dev/Core.lean').read_text(encoding='utf-8')
    p = (ROOT / 'StructuralS1RM20261018/CurrentPrefix.lean').read_text(encoding='utf-8')
    ns = s.index('namespace AMW.Cert.PC9QB6M\n')
    cs = s.rfind('noncomputable section\n', 0, ns)
    ce = s.index('end AMW.Cert.PC9QB6M\nend\n', ns) + len('end AMW.Cert.PC9QB6M\nend\n')
    dn = s.index('namespace AMW.Cert.PC9QB6MData\n')
    cov = s.index('noncomputable def COV :', dn)
    de = s.index('end AMW.Cert.PC9QB6MData\nend\n', cov) + len('end AMW.Cert.PC9QB6MData\nend\n')
    count_end = s.index('end OpethN.Counting\nend\n', de) + len('end OpethN.Counting\nend\n')
    notice = s.index('/-\nADDITIONAL THIRD-PARTY NOTICES AND LICENSE TEXTS', count_end)
    rename = lambda text: text.replace('PC9QB6M', 'PC9Tiny')
    # Compare only existing source segments in RAM. No prospective complete Lean
    # source is assembled, saved, hashed, imported or executed by this review.
    dcs = d.index('noncomputable section\nnamespace AMW.Cert.PC9Tiny\n')
    dce = d.index('end AMW.Cert.PC9Tiny\nend\n', dcs) + len('end AMW.Cert.PC9Tiny\nend\n')
    dcov = d.index('noncomputable def COV :', dce)
    dde = d.index('end AMW.Cert.PC9TinyData\nend\n', dcov) + len('end AMW.Cert.PC9TinyData\nend\n')
    dcount_end = d.index('end OpethN.Counting\nend\n', dde) + len('end OpethN.Counting\nend\n')
    dnotice = d.index('/-\nADDITIONAL THIRD-PARTY NOTICES AND LICENSE TEXTS', dcount_end)
    assert rename(s[cs:ce]) == d[dcs:dce]
    assert rename(s[cov:de]) == d[dcov:dde]
    assert rename(s[de:count_end]) == d[dde:dcount_end]
    assert s[notice:] == d[dnotice:]
    generator_tree = ast.parse((ROOT / 'research-goal-20261018-tiny-runtime-preparation/prepare_dev_sources.py').read_text(encoding='utf-8'))
    aliases = next(ast.literal_eval(n.value) for n in generator_tree.body
                   if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'ALIASES' for t in n.targets))
    assert d[dce:dcov] == '\n' + aliases
    table_start = s.index('noncomputable def TOP :', dn)
    prefix_table_start = p.index('noncomputable def TOP :', p.index('namespace AMW.Cert.PC9QB6MData\n'))
    prefix_table_end = p.index('end AMW.Cert.PC9QB6MData\n', prefix_table_start)
    assert s[table_start:cov].strip() == p[prefix_table_start:prefix_table_end].strip()
    payload = r'zfNat64\s+\d+\s+"[^"\n]*"'
    cpayload = re.findall(payload, s[cov:de])
    dpayload = re.findall(payload, d[dcov:dde])
    assert cpayload == dpayload and len(cpayload) == 137
    assert not any('PC9QB6M' in x for x in re.findall(r'"[^"\n]*"', s))
    assert byte_count('PC9QB6M') == byte_count('PC9Tiny') == 7
    retired = s[count_end:notice]
    retained_comments = re.findall(r'/-[\s\S]*?-/', retired)
    assert len(retained_comments) == 2
    assert all('Copyright (c) 2026 R. Arun Chandru.' in c and 'Apache-2.0' in c for c in retained_comments)
    assert sum(c.count('/-') for c in retained_comments) == retired.count('/-')
    retired_notices_bytes = sum(byte_count(c) + 1 for c in retained_comments)
    assert not re.search(r'zfNat64\s', retired)
    assert 'theorem candidate_strict_improvement' in retired
    assert 'namespace AMFinal' not in s[:count_end]  # Actual family is named differently below, retained only until generic counting.
    assert not re.search(r'(?m)^theorem candidate_', s[:count_end])
    assert not re.search(r'_private\.', s[:count_end])
    canonical_retained = byte_count(s[:count_end]) + retired_notices_bytes + byte_count(s[notice:])
    old_pair = byte_count(p) + byte_count(d)
    clients = [
        ('StructuralS1RTiny20261018.Phase1.Localization', 'StructuralS1RTiny20261018/Phase1/Localization.lean'),
        ('StructuralS1RTiny20261018.Phase2.Counting', 'StructuralS1RTiny20261018/Phase2/Counting.lean'),
        ('StructuralS1RTiny20261018.Phase4.Final', 'StructuralS1RTiny20261018/Phase4/Final.lean'),
    ]
    client_inventory = []
    internal_removed = 0
    for module, path in clients:
        blob = (ROOT / path).read_bytes()
        imports = [line for line in blob.splitlines(keepends=True) if line.startswith(b'import ')]
        assert all(line.startswith(b'import StructuralS1R') for line in imports)
        internal_removed += sum(map(len, imports))
        body = b''.join(line for line in blob.splitlines(keepends=True) if not line.startswith(b'import '))
        assert b'PC9QB6M' not in body and b'CurrentPrefix' not in body
        client_inventory.append({'module': module, 'path': path, 'bytes': len(blob),
            'imports_removed_bytes': sum(map(len, imports)), 'body_sha256': sha(body),
            'body_preserved_without_changes': True})
    gt = ast.parse((ROOT / 'research-goal-20261018-tiny-flatten-preparation-v3/generate_draft.py').read_text(encoding='utf-8'))
    old_modules = next(ast.literal_eval(n.value) for n in gt.body if isinstance(n, ast.Assign)
                       and any(isinstance(t, ast.Name) and t.id == 'MODULES' for t in n.targets))
    header = next(ast.literal_eval(n.value.func.value).encode('utf-8') for n in gt.body if isinstance(n, ast.Assign)
                  and any(isinstance(t, ast.Name) and t.id == 'HEADER' for t in n.targets))
    separator_size = lambda module: byte_count('\n/- BEGIN FLATTENED MODULE ' + module + ' -/\n')
    new_core_module = 'StructuralS1RTiny20261018.Production.Core'
    proposed_input_bytes = canonical_retained + sum(x['bytes'] for x in client_inventory)
    wrapper = (ROOT / 'research-goal-20261018-tiny-flatten-preparation-v3/official-wrapper.lean.txt').read_bytes()
    # Moving unchanged external imports to the header preserves their total byte
    # count. Three client import blocks disappear; canonical has no user import.
    proposed_with_unchanged_header_and_separator_format = (
        proposed_input_bytes - internal_removed + len(header) + 1 + len(wrapper) + 1
        + separator_size(new_core_module) + sum(separator_size(m) for m, _ in clients) + 4)
    prep = json.loads((ROOT / 'research-goal-20261018-tiny-flatten-preparation-v3/preparation.json').read_text())
    current_flatten_bytes = prep['predicted_solution_bytes']
    assert current_flatten_bytes == 1979280
    imports = [line.decode('ascii').strip()[7:] for line in s.encode().splitlines(keepends=True) if line.startswith(b'import ')]
    assert len(imports) == 24 and not any(x.startswith('StructuralS1R') for x in imports)
    family_names = sorted(set(re.findall(r'\bPC9QB6M[A-Za-z_0-9]*', s[:count_end])))
    exporter = (ROOT / 'tmp/setup-20261015/packages/lean4export/Export.lean').read_text()
    assert 'for c in e.getUsedConstants do\n      dumpConstant c' in exporter
    assert 'dumpDeps val.type\n    dumpDeps val.value' in exporter
    report = {
        'schema': 'tiny-canonical-dedup-read-only-feasibility-v1',
        'reviewed_at_utc': datetime.now(timezone.utc).isoformat(),
        'candidate_sources_generated': 0, 'candidate_compilations': 0,
        'new_math_evaluations': 0, 'network_requests': 0, 'existing_inputs_modified': False,
        'conditional_use': 'Only if the current cold attempt fails its total deadline; success makes implementation unnecessary',
        'feasible_at_source_and_dependency_level': True,
        'required_name_family_replacement': {'from': 'PC9QB6M', 'to': 'PC9Tiny',
            'same_utf8_length': True, 'identifier_family_tokens': family_names,
            'matches_inside_string_literals': 0},
        'identical_existing_Dev_proof_segments_after_name_replacement': {
            'strengthened_concrete_checker_TinyGoal': True, 'COV_walk_payloads_and_cut_witnesses': True,
            'reflection_actual_W9_counting_tail': True, 'full_license_trailer': True},
        'data_table_identity': {'canonical_table_block_equals_prefix': True,
            'proposed_actual_definitions_replace_existing_ten_aliases': True,
            'alias_names': ['TOP','BK','lbS','TOPD','BKD','lbD','REG','hR','PT','ptS'],
            'raw_cover_payloads_137_byte_equal': True},
        'retirement': {'cut_after': 'end OpethN.Counting\nend\n',
            'restore_original_license_from_marker': 'ADDITIONAL THIRD-PARTY NOTICES AND LICENSE TEXTS',
            'retired_legacy_tail_bytes': byte_count(retired),
            'retired_tail_contains_copyright_or_license_notice': True,
            'all_two_retired_copyright_blocks_retained_verbatim': True,
            'retained_copyright_blocks_plus_newlines_bytes': retired_notices_bytes,
            'removed_old_concrete_has_equivalent_retained_strengthened_code': True},
        'source_bytes': {'current_prefix_plus_Dev_Core': old_pair,
            'canonical_original': byte_count(s), 'canonical_retained': canonical_retained,
            'raw_core_savings': old_pair - canonical_retained,
            'client_inputs': client_inventory,
            'proposed_four_input_total': proposed_input_bytes,
            'internal_client_import_bytes_removed': internal_removed,
            'current_five_input_flatten': current_flatten_bytes,
            'hypothetical_module_name_for_byte_accounting': new_core_module,
            'hypothetical_same_format_flatten_bytes': proposed_with_unchanged_header_and_separator_format,
            'hypothetical_flatten_savings': current_flatten_bytes - proposed_with_unchanged_header_and_separator_format,
            'hypothetical_source_headroom_to_2000000': 2000000 - proposed_with_unchanged_header_and_separator_format,
            'extra_production_notice_bytes_not_included': True},
        'external_imports': imports,
        'clients_keep_namespaces_statements_and_bodies': True,
        'all_copyright_license_and_mathematical_payload_retention_required': True,
        'performance_conclusions': {
            'ordinary_elaboration_and_module_import_redundancy_removed': True,
            'old_exporter_uses_requested_roots_transitive_dependency_closure': True,
            'old_unused_PC9_checker_may_already_be_absent_from_export': True,
            'Comparator_default_kernel_or_nanoda_runtime_reduction_proven': False,
            'new_total_3200s_success_proven': False},
        'unproven_gates': ['actual production-only generator and retention audit',
            'whole new-source ordinary elaboration and permitted axioms',
            'fresh public statements/dependencies/primitives comparison',
            'Lean default kernel and nanoda replay', 'one complete 3200s attempt'],
        'input_pins': before,
    }
    assert before == [row(n) for n in list(PINS) + EXTRA]
    write('feasibility.json', report)
    owned = [row(p.relative_to(ROOT).as_posix()) for p in sorted(HERE.iterdir()) if p.is_file()]
    write('files.json', {'schema': 'tiny-dedup-read-only-review-files-v1', 'files': owned,
        'dependencies': before, 'all_inputs_unchanged': True, 'source_generation_count': 0,
        'Lean_runs': 0, 'mathematical_evaluations': 0, 'network_requests': 0})
    print(json.dumps({'report_manifest_sha256': sha((HERE / 'files.json').read_bytes()),
        'hypothetical_flatten_bytes': proposed_with_unchanged_header_and_separator_format,
        'source_savings': current_flatten_bytes - proposed_with_unchanged_header_and_separator_format,
        'candidate_sources_generated': 0}))

if __name__ == '__main__':
    main()
