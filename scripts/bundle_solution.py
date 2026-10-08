"""Bundle local proof modules without changing any encoded natural number.

The default output is an explicitly incomplete draft in ignored tmp storage.
This script does not compile Lean or authorize a record submission.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re

ALPHABET = ''.join(chr(n) for n in range(33, 127) if n not in (34, 92))
BASE64 = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'
DEFAULT_MODULES = ['RecordProportion.AnalyticBridge', 'RecordProportion.FiniteCertificate']
MACRO = '''namespace RHWeilSubmissionEncoding
private def digit92 (c : Char) : Nat :=
  let n := c.toNat - 33
  if 92 < c.toNat then n - 2 else if 34 < c.toNat then n - 1 else n
private def decode92 (s : String) : Nat :=
  s.toList.foldl (fun n c => n * 92 + digit92 c) 0
macro "n% " s:str : term => do
  let n := decode92 s.getString
  return Lean.Syntax.mkNumLit (toString n)
end RHWeilSubmissionEncoding
'''

def encode(n: int) -> str:
    if not n:
        return ALPHABET[0]
    digits = []
    while n:
        n, remainder = divmod(n, 92); digits.append(ALPHABET[remainder])
    return ''.join(reversed(digits))

def decode(s: str) -> int:
    n = 0
    for c in s:
        n = n * 92 + ALPHABET.index(c)
    return n

def compact_hex(source: str) -> tuple[str, int, int]:
    """Only rewrite long hex literals outside strings and nested comments."""
    out = []
    i = replaced = saved = depth = 0
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                out.append('/-'); i += 2; depth += 1
            elif source.startswith('-/', i):
                out.append('-/'); i += 2; depth -= 1
            else:
                out.append(source[i]); i += 1
        elif source.startswith('/-', i):
            out.append('/-'); i += 2; depth = 1
        elif source.startswith('--', i):
            j = source.find('\n', i)
            if j < 0: j = len(source)
            out.append(source[i:j]); i = j
        elif source.startswith('n64%', i):
            match = re.match(r'n64%\s*"([A-Za-z0-9+/]+)"', source[i:])
            if match is None:
                out.append(source[i]); i += 1; continue
            value = 0
            for char in match.group(1): value = value * 64 + BASE64.index(char)
            encoded = encode(value)
            assert decode(encoded) == value
            replacement = 'n% "' + encoded + '"'
            out.append(replacement); replaced += 1
            saved += len(match.group(0)) - len(replacement)
            i += len(match.group(0))
        elif source[i] == '"':
            j = i + 1
            while j < len(source):
                if source[j] == '\\': j += 2
                elif source[j] == '"': j += 1; break
                else: j += 1
            out.append(source[i:j]); i = j
        elif source.startswith('0x', i) and (i == 0 or not (source[i-1].isalnum() or source[i-1] in "_'")):
            match = re.match(r'0x[0-9a-fA-F]+', source[i:])
            if match is None:
                out.append(source[i]); i += 1; continue
            literal = match.group(0)
            if len(literal) < 60:
                out.append(literal)
            else:
                value = int(literal, 16)
                encoded = encode(value)
                assert decode(encoded) == value
                replacement = '(n% "' + encoded + '")'
                if len(replacement) < len(literal):
                    out.append(replacement); replaced += 1
                    saved += len(literal) - len(replacement)
                else: out.append(literal)
            i += len(literal)
        else:
            out.append(source[i]); i += 1
    assert depth == 0, 'Unclosed source comment'
    return ''.join(out), replaced, saved

def compact_layout(source: str) -> tuple[str, int]:
    """Drop explanatory comments, keeping attribution blocks and code layout.

    Newlines inside removed comments remain in place until empty-line removal.
    Strings and nested block comments are scanned rather than regex-replaced.
    Compilation of the resulting complete file remains mandatory.
    """
    out = []
    i = removed = 0
    while i < len(source):
        if source.startswith('/-', i):
            j, depth = i + 2, 1
            while j < len(source) and depth:
                if source.startswith('/-', j): j += 2; depth += 1
                elif source.startswith('-/', j): j += 2; depth -= 1
                else: j += 1
            assert depth == 0, 'Unclosed source comment'
            comment = source[i:j]
            keep = any(word in comment.lower() for word in
                       ['copyright', 'attribution', 'apache', 'licensed'])
            if keep:
                out.append(comment)
            else:
                out.append(' ' + '\n' * comment.count('\n')); removed += 1
            i = j
        elif source.startswith('--', i):
            j = source.find('\n', i)
            if j < 0: j = len(source)
            comment = source[i:j]
            if any(word in comment.lower() for word in ['copyright', 'attribution', 'licensed']):
                out.append(comment)
            else:
                out.append(' '); removed += 1
            i = j
        elif source[i] == '"':
            j = i + 1
            while j < len(source):
                if source[j] == '\\': j += 2
                elif source[j] == '"': j += 1; break
                else: j += 1
            out.append(source[i:j]); i = j
        else:
            out.append(source[i]); i += 1
    return '\n'.join(line.rstrip() for line in ''.join(out).splitlines()
                     if line.strip()) + '\n', removed


def local_imports(source: str) -> list[str]:
    return [name for line in source.splitlines() if line.startswith('import ')
            for name in line[7:].split() if name.startswith('RecordProportion.')]


def dependency_order(root: Path, modules: list[str]) -> list[Path]:
    """Read actual local imports, rejecting missing files and dependency cycles."""
    paths = []
    visited = set()
    active = set()
    def visit(module: str) -> None:
        if module in visited:
            return
        if module in active:
            raise ValueError('Local import cycle: ' + module)
        if not re.fullmatch(r'RecordProportion\.[A-Za-z_][A-Za-z_0-9]*', module):
            raise ValueError('Unsupported local module: ' + module)
        path = root.joinpath(*module.split('.')).with_suffix('.lean')
        source = path.read_text(encoding='utf-8-sig')
        active.add(module)
        for dependency in local_imports(source):
            visit(dependency)
        active.remove(module)
        visited.add(module)
        paths.append(path)
    for module in modules:
        visit(module)
    return paths


def code_mask(source: str) -> str:
    """Mask strings and nested comments without changing line positions."""
    out = list(source)
    i = 0
    def mask(first: int, last: int) -> None:
        for k in range(first, last):
            if source[k] != '\n':
                out[k] = ' '
    while i < len(source):
        start = i
        if source.startswith('/-', i):
            i += 2
            depth = 1
            while i < len(source) and depth:
                if source.startswith('/-', i): i += 2; depth += 1
                elif source.startswith('-/', i): i += 2; depth -= 1
                else: i += 1
            if depth:
                raise ValueError('Unclosed source comment')
            mask(start, i)
        elif source.startswith('--', i):
            i = source.find('\n', i)
            if i < 0: i = len(source)
            mask(start, i)
        elif source[i] == '"':
            i += 1
            closed = False
            while i < len(source):
                if source[i] == '\\': i += 2
                elif source[i] == '"': i += 1; closed = True; break
                else: i += 1
            if not closed:
                raise ValueError('Unclosed source string')
            mask(start, i)
        else:
            i += 1
    return ''.join(out)


def remaining_sections(source: str) -> int:
    """Recognize these modules' explicit top-level scopes; fail on mismatches.

    Named namespaces/sections must already be closed by their source. Lean
    allows anonymous sections to remain open at end of a module; the bundle
    closes those explicitly before ending its module-isolation section.
    """
    scopes = []
    identifier = r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*'
    for line in code_mask(source).splitlines():
        line = line.rstrip()
        if not re.match(r'^(?:namespace|(?:noncomputable )?section|end)\b', line):
            continue
        match = re.fullmatch(r'(namespace|(?:noncomputable )?section|end)(?:\s+(' + identifier + r'))?', line)
        if not match:
            raise ValueError('Unsupported scope syntax: ' + line)
        command, name = match.groups()
        if command == 'namespace':
            if name is None:
                raise ValueError('Unnamed namespace')
            scopes.extend(name.split('.'))
        elif command.endswith('section'):
            scopes.extend(name.split('.') if name else [None])
        else:
            expected = name.split('.') if name else [None]
            if len(scopes) < len(expected) or scopes[-len(expected):] != expected:
                raise ValueError('Mismatched scope: ' + line)
            del scopes[-len(expected):]
    if any(name is not None for name in scopes):
        raise ValueError('Unclosed named source scope: ' + str(scopes))
    return len(scopes)

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('tmp/bundles/Solution.draft.lean'))
    parser.add_argument('--entry', type=Path, help='Optional proved candidate assembly module')
    parser.add_argument('--module', action='append', help='Local root module; defaults to the analytic and finite chains')
    parser.add_argument('--compact-layout', action='store_true',
                        help='Remove non-attribution comments and empty lines; still requires full compilation')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    modules = args.module or DEFAULT_MODULES
    entry = (root/args.entry).resolve() if args.entry else None
    if entry is not None:
        if not entry.is_relative_to(root):
            parser.error('Entry must stay inside this repository')
        modules = modules + local_imports(entry.read_text(encoding='utf-8-sig'))
    names = dependency_order(root, modules)
    if entry is not None: names.append(entry)
    imports = {'Lean', 'ChallengeDeps.CandidateSpec'}
    payloads = []; sources = []; replaced = saved = 0
    for module_index, path in enumerate(names):
        source = path.read_text(encoding='utf-8-sig')
        open_sections = remaining_sections(source)
        sources.append({'path': path.relative_to(root).as_posix(),
                        'sha256': hashlib.sha256(source.encode()).hexdigest(),
                        'anonymous_sections_closed': open_sections})
        lines = []
        for line in source.splitlines():
            if line.startswith('import '):
                for name in line[7:].split():
                    if not name.startswith('RecordProportion.'): imports.add(name)
            elif not line.startswith('#print axioms '):
                lines.append(line.rstrip())
        body = '\n'.join(lines) + '\n'
        body, count, reduction = compact_hex(body)
        replaced += count; saved += reduction
        section = 'RHWeilBundleModule_' + str(module_index)
        payloads.append('/- Source: ' + path.relative_to(root).as_posix() + ' -/\n' +
                        'section ' + section + '\n' + body + 'end\n' * open_sections +
                        'end ' + section + '\n')
    header = '/- Copyright 2026 Li Xiang (lixiang90). Apache-2.0.\n' \
             'Derived-source notices are retained below and in NOTICE.\n' \
             'Generated draft; compilation and official verification are separate. -/\n'
    result = header + ''.join('import '+name+'\n' for name in sorted(imports)) + '\n' + MACRO + '\n'.join(payloads)
    comments_removed = layout_bytes_saved = 0
    if args.compact_layout:
        before = len(result.encode())
        result, comments_removed = compact_layout(result)
        notice = (root/'NOTICE').read_text(encoding='utf-8-sig')
        assert '/-' not in notice and '-/' not in notice
        result = '/- Retained distribution notices:\n' + notice + '\n-/\n' + result
        layout_bytes_saved = before - len(result.encode())
    actual_declarations = {name: bool(re.search(r'^theorem\s+'+name+r'\s*:', result, re.M))
        for name in ['candidate_strict_improvement', 'candidate_critical_line_bound',
                     'candidate_critical_line_bound_cumulative']}
    out = (root/args.output).resolve()
    assert out.is_relative_to(root), 'Output must stay inside this repository'
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(result, encoding='utf-8', newline='\n')
    metadata = {'status': 'draft_not_verified', 'sources': sources,
        'module_scope_policy': 'ordinary named section per module; anonymous source sections closed explicitly',
        'output': out.relative_to(root).as_posix(), 'bytes': len(result.encode()),
        'sha256': hashlib.sha256(result.encode()).hexdigest(),
        'hex_literals_compacted': replaced, 'source_bytes_saved': saved,
        'compact_layout': args.compact_layout, 'comments_removed': comments_removed,
        'layout_bytes_saved': layout_bytes_saved,
        'limit_bytes': 2000000, 'within_source_limit': len(result.encode()) <= 2000000,
        'candidate_declarations_present': actual_declarations,
        'submitted': False}
    out.with_suffix('.manifest.json').write_text(json.dumps(metadata, indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in metadata.items() if k != 'sources'}, indent=2))

if __name__ == '__main__': main()
