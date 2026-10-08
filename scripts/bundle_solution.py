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
ORDER = ['ImportedAM', 'FiniteCertificateData', 'FloydSoundness', 'FiniteCertificate', 'Majorant',
         'AnalyticBridge', 'CountBridge']
MACRO = '''namespace RHWeilSubmissionEncoding
private def digit92 (c : Char) : Nat :=
  let n := c.toNat - 33
  if 92 < c.toNat then n - 2 else if 34 < c.toNat then n - 1 else n
private def decode92 (s : String) : Nat :=
  s.toList.foldl (fun n c => n * 92 + digit92 c) 0
macro "rhNat92% " s:str : term => do
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
            replacement = 'rhNat92% "' + encoded + '"'
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
                replacement = '(rhNat92% "' + encoded + '")'
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

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('tmp/bundles/Solution.draft.lean'))
    parser.add_argument('--entry', type=Path, help='Optional proved candidate assembly module')
    parser.add_argument('--compact-layout', action='store_true',
                        help='Remove non-attribution comments and empty lines; still requires full compilation')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    names = [root/'RecordProportion'/f'{name}.lean' for name in ORDER]
    if args.entry: names.append((root/args.entry).resolve())
    imports = {'Lean', 'ChallengeDeps.CandidateSpec'}
    payloads = []; sources = []; replaced = saved = 0
    for path in names:
        source = path.read_text(encoding='utf-8-sig')
        sources.append({'path': path.relative_to(root).as_posix(),
                        'sha256': hashlib.sha256(source.encode()).hexdigest()})
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
        payloads.append('/- Source: ' + path.relative_to(root).as_posix() + ' -/\n' + body)
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
