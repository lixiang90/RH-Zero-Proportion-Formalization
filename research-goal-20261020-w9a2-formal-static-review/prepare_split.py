"""Source-only development split and inverse-merge check; never invokes Lean."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
SOURCE = ROOT / 'StructuralW9A220261020/Core.lean'
EXPECTED = 'c5180e8cb9d219bec5cf29e4d65e0cfc304f4d40a12ad6d52332603e115fccd6'
MARKER = b'-- SWAP BEGIN certificate:'
PROLOGUE = (b'import StructuralW9A220261020.Prefix\n'
            b'set_option Elab.async false\n'
            b'set_option linter.all false\n')
PREFIX_CLOSE = b'end -- development split closes the original anonymous section\n'


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def clean_lean(text):
    out = []
    i = 0
    depth = 0
    quoted = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                out.extend('  ')
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                out.extend('  ')
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif quoted:
            if text[i] == '\\':
                out.extend('  ')
                i += 2
            elif text[i] == '"':
                quoted = False
                out.append(' ')
                i += 1
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            out.extend('  ')
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            if end < 0:
                end = len(text)
            out.extend(' ' * (end - i))
            i = end
        elif text[i] == '"':
            quoted = True
            out.append(' ')
            i += 1
        else:
            out.append(text[i])
            i += 1
    assert not depth and not quoted
    return ''.join(out)


def main():
    raw = SOURCE.read_bytes()
    assert digest(raw) == EXPECTED and raw.count(MARKER) == 1
    cut = raw.index(MARKER)
    prefix, suffix = raw[:cut], raw[cut:]
    ptext = clean_lean(prefix.decode('utf-8'))
    stext = clean_lean(suffix.decode('utf-8'))
    private_names = re.findall(r'^private\s+(?:def|theorem|lemma|abbrev|instance)\s+([^\s:{(]+)', ptext, re.M)
    private_uses = {name: len(re.findall(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])", stext))
                    for name in private_names}
    assert len(private_names) == 5 and all(n == 0 for n in private_uses.values())
    scopes = []
    states = [{'options': {}, 'ambient': []}]
    for line_no, line in enumerate(ptext.splitlines(), 1):
        if re.match(r'^(?:(?:noncomputable )?section\b|namespace\s)', line):
            scopes.append({'line': line_no, 'command': line.strip()})
            states.append({'options': dict(states[-1]['options']), 'ambient': []})
        elif re.match(r'^end(?:\s|$)', line):
            assert scopes
            scopes.pop()
            states.pop()
        elif re.match(r'^set_option ', line) and not line.rstrip().endswith(' in'):
            fields = line.split()
            states[-1]['options'][fields[1]] = ' '.join(fields[2:])
        elif re.match(r'^(open |open scoped |variable|attribute|local |notation|scoped )', line):
            states[-1]['ambient'].append({'line': line_no, 'command': line.strip()})
    assert scopes == [{'line': 6661, 'command': 'section'}]
    assert states[-1]['options'] == {'Elab.async': 'false', 'linter.all': 'false'}
    assert not any(s['ambient'] for s in states)
    drafts = HERE / 'development-split/StructuralW9A220261020'
    drafts.mkdir(parents=True, exist_ok=False)
    artifacts = {'Prefix.lean': prefix + PREFIX_CLOSE, 'Core.lean': PROLOGUE + suffix}
    for name, data in artifacts.items():
        with (drafts / name).open('xb') as stream:
            stream.write(data)
    assert (drafts / 'Prefix.lean').read_bytes().endswith(PREFIX_CLOSE)
    reconstructed = (drafts / 'Prefix.lean').read_bytes()[:-len(PREFIX_CLOSE)] + (drafts / 'Core.lean').read_bytes()[len(PROLOGUE):]
    assert reconstructed == raw and digest(SOURCE.read_bytes()) == EXPECTED
    out = {
        'status': 'PASS_STATIC_DEVELOPMENT_SPLIT_ONLY_NOT_COMPILED',
        'full_source_unchanged_sha256': EXPECTED,
        'split_before_full_source_line': prefix.count(b'\n') + 1,
        'private_decl_suffix_token_uses': private_uses,
        'open_scopes_at_boundary': scopes,
        'open_namespaces_at_boundary': [],
        'unexported_ambient_options_recreated_in_suffix': states[-1]['options'],
        'other_unexported_ambient_commands': [],
        'suffix_prologue': PROLOGUE.decode('ascii'),
        'prefix_added_closing_command': PREFIX_CLOSE.decode('ascii'),
        'inverse_merge_byte_equal': True,
        'inverse_merge_sha256': digest(reconstructed),
        'prefix_public_constants_and_syntax_imported_by_original_names': True,
        'caveat': 'The original unnamed section is explicitly closed only in the development Prefix; suffix resets module-local option scope and explicitly recreates the only two active options. There are no active open/open scoped/variable/local commands at the original cut. Actual import/elaboration still requires the root frozen ordinary gate. No production verification or timing claim.',
        'artifacts': [{'path': (drafts / name).relative_to(ROOT).as_posix(),
                       'bytes': len(data), 'sha256': digest(data)}
                      for name, data in artifacts.items()],
        'added_development_bytes': len(PROLOGUE) + len(PREFIX_CLOSE),
        'compiler_runs': 0,
        'candidate_mutations': 0,
    }
    with (HERE / 'split-audit.json').open('x', encoding='utf-8', newline='\n') as stream:
        json.dump(out, stream, ensure_ascii=False, indent=2)
        stream.write('\n')
    print(json.dumps(out, ensure_ascii=False))


if __name__ == '__main__':
    main()
