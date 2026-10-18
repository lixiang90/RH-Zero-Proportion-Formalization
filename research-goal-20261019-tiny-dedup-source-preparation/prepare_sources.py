"""Pure text preparation of four equivalent production modules, not a flatten run.

No Lean, exporter, kernel, mathematical evaluator, network or full upload-source
generator is invoked. Frozen canonical/development sources are never modified.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OUT = ROOT / 'StructuralS1RTiny20261018/Production'
CANONICAL_PIN = '9fbdf3f2dc62333b636d3b25dfb3bf2b15e3b8c628ece73d6ba1bc768fc5f1a6'
REVIEW_PIN = '5e100daa5e14cf4445af8d88dd826a934a1f3e9f5bd5f6a03d83727006ef35eb'
FAILURE_PIN = '3dcf11c64bebda5b543a52edc43041664d314ddc9855a8330240843ccf875747'
CLIENTS = {
    'Localization.lean': 'StructuralS1RTiny20261018/Phase1/Localization.lean',
    'Counting.lean': 'StructuralS1RTiny20261018/Phase2/Counting.lean',
    'Final.lean': 'StructuralS1RTiny20261018/Phase4/Final.lean',
}

def sha(blob):
    return hashlib.sha256(blob).hexdigest()

def row(p):
    p = Path(p); b = p.read_bytes()
    return {'path': p.relative_to(ROOT).as_posix(), 'bytes': len(b), 'sha256': sha(b)}

def write(path, blob):
    with path.open('xb') as f:
        f.write(blob)

def main():
    assert not OUT.exists(), 'Exclusive versioned Production source directory already exists'
    canonical = ROOT / 'StructuralS1RTiny20261018/Core.lean'
    review = ROOT / 'research-goal-20261019-tiny-dedup-static-review/report-files.json'
    failure = ROOT / 'tmp/current-s1r-tiny-20261018/production-v0/failure.json'
    assert row(canonical)['sha256'] == CANONICAL_PIN
    assert row(review)['sha256'] == REVIEW_PIN
    assert row(failure)['sha256'] == FAILURE_PIN
    failed = json.loads(failure.read_text(encoding='utf-8'))
    assert failed['failed'] is True and failed['local_single_file_verified'] is False
    assert failed['stage'] == 'nanoda' and failed['error_type'] == 'TimeoutExpired'
    audit = json.loads((review.parent / 'feasibility.json').read_text(encoding='utf-8'))
    for pin in audit['input_pins']:
        assert row(ROOT / pin['path'])['sha256'] == pin['sha256']
    dependencies = [canonical, review, review.parent / 'feasibility.json', failure,
                    ROOT / 'StructuralS1RTiny20261018/Dev/Core.lean',
                    ROOT / 'StructuralS1RM20261018/CurrentPrefix.lean',
                    *[ROOT / p for p in CLIENTS.values()],
                    ROOT / 'research-goal-20261018-tiny-flatten-preparation-v3/official-wrapper.lean.txt']
    before = [row(p) for p in dependencies]
    s = canonical.read_bytes()
    cut = s.index(b'end OpethN.Counting\nend\n') + len(b'end OpethN.Counting\nend\n')
    notice = s.index(b'/-\nADDITIONAL THIRD-PARTY NOTICES AND LICENSE TEXTS', cut)
    retired = s[cut:notice]
    comments = re.findall(rb'/-[\s\S]*?-/', retired)
    assert len(comments) == 2
    assert all(b'Copyright (c) 2026 R. Arun Chandru.' in c and b'Apache-2.0' in c for c in comments)
    assert sum(c.count(b'/-') for c in comments) == retired.count(b'/-')
    retained = s[:cut] + b''.join(c + b'\n' for c in comments) + s[notice:]
    assert not any(b'PC9QB6M' in q for q in re.findall(rb'"[^"\n]*"', retained))
    core = retained.replace(b'PC9QB6M', b'PC9Tiny')
    assert len(core) == len(retained) == 1815476
    assert b'PC9QB6M' not in core
    assert not re.search(rb'(?m)^(?:private )?theorem candidate_', core)
    assert b'import StructuralS1R' not in core
    assert len(re.findall(rb'zfNat64\s+\d+\s+"[^"\n]*"', core)) == 137
    payload = lambda blob: re.findall(rb'zfNat64\s+\d+\s+"[^"\n]*"', blob)
    assert payload(core) == payload(s)
    outputs = {'Core.lean': core}
    import_changes = {}
    for target, source in CLIENTS.items():
        old = (ROOT / source).read_bytes()
        new = old.replace(b'import StructuralS1RTiny20261018.Dev.Core\n',
                          b'import StructuralS1RTiny20261018.Production.Core\n')
        new = new.replace(b'import StructuralS1RTiny20261018.Phase1.Localization\n',
                          b'import StructuralS1RTiny20261018.Production.Localization\n')
        new = new.replace(b'import StructuralS1RTiny20261018.Phase2.Counting\n',
                          b'import StructuralS1RTiny20261018.Production.Counting\n')
        body = lambda b: b''.join(x for x in b.splitlines(keepends=True) if not x.startswith(b'import '))
        assert body(old) == body(new)
        assert old != new
        outputs[target] = new
        import_changes[target] = {'prior': source, 'old_import_lines': [x.decode().strip() for x in old.splitlines() if x.startswith(b'import ')],
            'new_import_lines': [x.decode().strip() for x in new.splitlines() if x.startswith(b'import ')],
            'non_import_body_sha256': sha(body(new)), 'all_non_import_bytes_unchanged': True}
    assert before == [row(p) for p in dependencies]
    OUT.mkdir()
    for name, data in outputs.items():
        write(OUT / name, data)
    description = {
        'schema': 'tiny-dedup-equivalent-production-modules-prepared-v1',
        'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
        'scope': 'Four pure text module inputs only; full upload-source generator and all verification remain unexecuted',
        'files': [row(OUT / p) for p in outputs] + [row(Path(__file__))],
        'dependencies': before, 'source_core_bytes': len(core),
        'source_modules_total_bytes': sum(map(len, outputs.values())),
        'namespace_family_mapping': {'PC9QB6M': 'PC9Tiny'},
        'canonical_kept_prefix_bytes': cut, 'canonical_full_license_trailer_bytes': len(s) - notice,
        'canonical_two_retired_copyright_blocks_bytes_with_newlines': sum(len(c) + 1 for c in comments),
        'canonical_retired_code_removed_bytes': len(retired) - sum(len(c) + 1 for c in comments),
        'all_payloads_137_byte_identical': True,
        'all_canonical_copyright_blocks_and_full_license_preserved': True,
        'all_existing_Dev_strengthened_semantics_and_witnesses_retained': True,
        'no_old_covered_assumption_substituted': True,
        'client_import_only_changes': import_changes,
        'trusted_constants_defined_or_modified': False,
        'old_failure_preserved_and_not_accepted_as_complete': True,
        'old_inputs_modified': False, 'candidate_flatten_generator_executions': 0,
        'Lean_runs': 0, 'export_Comparator_nanoda_runs': 0, 'mathematical_evaluations': 0,
        'network_requests': 0, 'future_fresh_3200s_gate_required': True,
        'official_website_acceptance': False,
    }
    assert before == [row(p) for p in dependencies]
    write(HERE / 'prepared-files.json', (json.dumps(description, ensure_ascii=False, indent=2) + '\n').encode())
    print(json.dumps({'prepared_sha256': sha((HERE / 'prepared-files.json').read_bytes()),
                     'source_modules_total_bytes': description['source_modules_total_bytes'],
                     'full_upload_generator_executions': 0}))

if __name__ == '__main__':
    main()
