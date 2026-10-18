"""Version the static audit to retain the two copyright blocks found in old tail."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent

def sha(b):
    return hashlib.sha256(b).hexdigest()

def main():
    old = HERE / 'audit_static.py'
    source = old.read_text(encoding='utf-8')
    marker = "    assert not re.search(r'Copyright|SPDX-License-Identifier|Authors?:|Apache License', retired)"
    assert source.count(marker) == 1
    source = source.replace(marker, """    retained_comments = re.findall(r'/-[\\s\\S]*?-/', retired)
    assert len(retained_comments) == 2
    assert all('Copyright (c) 2026 R. Arun Chandru.' in c and 'Apache-2.0' in c for c in retained_comments)
    assert sum(c.count('/-') for c in retained_comments) == retired.count('/-')
    retired_notices_bytes = sum(byte_count(c) + 1 for c in retained_comments)
    assert not re.search(r'zfNat64\\s', retired)""")
    source = source.replace('canonical_retained = byte_count(s[:count_end]) + byte_count(s[notice:])',
        'canonical_retained = byte_count(s[:count_end]) + retired_notices_bytes + byte_count(s[notice:])')
    source = source.replace("'retired_tail_contains_copyright_or_license_notice': False,",
        "'retired_tail_contains_copyright_or_license_notice': True,\n            'all_two_retired_copyright_blocks_retained_verbatim': True,\n            'retained_copyright_blocks_plus_newlines_bytes': retired_notices_bytes,")
    with (HERE / 'audit_static_v1.py').open('x', encoding='utf-8', newline='\n') as f:
        f.write(source)
    with (HERE / 'first-attempt-terminal.json').open('x', encoding='utf-8', newline='\n') as f:
        json.dump({'exit_code': 1, 'script': old.name, 'script_sha256': sha(old.read_bytes()),
            'failed_assertion': "not re.search(r'Copyright|SPDX-License-Identifier|Authors?:|Apache License', retired)",
            'meaning': 'The legacy tail contains two copyright notices; a correct fallback must preserve them',
            'candidate_source_generated': False, 'Lean_runs': 0, 'inputs_changed': False}, f, indent=2); f.write('\n')
    print(json.dumps({'static_audit_versioned': True, 'candidate_sources_generated': 0}))

if __name__ == '__main__':
    main()
