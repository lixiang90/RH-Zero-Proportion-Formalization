"""Reproduce the website-ready Gram-defect Solution.lean, without numeral rewriting.

The old finite certificate in Core is replaced by the scaled certificate,
not concatenated with it. Shared PCell proof helpers and all source notices
remain. Anonymous sections implicitly closed at each original module EOF
are explicitly closed before the next module, and module-local open/option
commands are isolated in named sections. Compilation is a separate check.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re

BEGIN = '-- SWAP BEGIN certificate'
END = '-- SWAP END certificate'
HELPER_START = 'noncomputable section\nnamespace AMW.Cert.PCell\nopen AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD\ndef pwD '
HELPER_END = 'end AMW.Cert.PCell\nend\n'
TRAILER = '/-\nADDITIONAL THIRD-PARTY NOTICES AND LICENSE TEXTS'
MAX_BYTES = 2_000_000


def code_mask(source: str) -> str:
    """Mask nested comments and strings while preserving offsets and newlines."""
    chars = list(source)
    i = 0
    depth = 0
    string = False
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                chars[i:i + 2] = [' ', ' ']; depth += 1; i += 2
            elif source.startswith('-/', i):
                chars[i:i + 2] = [' ', ' ']; depth -= 1; i += 2
            else:
                if source[i] != '\n': chars[i] = ' '
                i += 1
        elif string:
            if source[i] == '\\':
                chars[i] = ' '; i += 1
                if i < len(source):
                    if source[i] != '\n': chars[i] = ' '
                    i += 1
            else:
                if source[i] == '"': string = False
                if source[i] != '\n': chars[i] = ' '
                i += 1
        elif source.startswith('/-', i):
            chars[i:i + 2] = [' ', ' ']; depth = 1; i += 2
        elif source.startswith('--', i):
            end = source.find('\n', i)
            if end < 0: end = len(source)
            chars[i:end] = [' '] * (end - i); i = end
        elif source[i] == '"':
            chars[i] = ' '; string = True; i += 1
        else:
            i += 1
    if depth or string:
        raise ValueError('Unterminated source comment or string')
    return ''.join(chars)


def remaining_sections(source: str) -> int:
    """Parse the exact top-level scope syntax used by these five modules."""
    scopes: list[str | None] = []
    identifier = r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*'
    for line_number, line in enumerate(code_mask(source).splitlines(), 1):
        line = line.rstrip()
        if not re.match(r'^(?:namespace|(?:noncomputable )?section|end)\b', line):
            continue
        match = re.fullmatch(r'(namespace|(?:noncomputable )?section|end)(?:\s+(' + identifier + r'))?', line)
        if not match:
            raise ValueError(f'Unsupported scope syntax at {line_number}: {line}')
        command, name = match.groups()
        if command == 'namespace':
            if name is None: raise ValueError('Unnamed namespace')
            scopes.extend(name.split('.'))
        elif command.endswith('section'):
            scopes.extend(name.split('.') if name else [None])
        else:
            expected = name.split('.') if name else [None]
            if len(scopes) < len(expected) or scopes[-len(expected):] != expected:
                raise ValueError(f'Mismatched scope at {line_number}: {line}')
            del scopes[-len(expected):]
    if any(name is not None for name in scopes):
        raise ValueError('Unclosed named source scope: ' + repr(scopes))
    return len(scopes)


def strip_imports(source: str) -> tuple[str, set[str]]:
    mask_lines = code_mask(source).splitlines()
    lines = source.splitlines()
    imports: set[str] = set()
    result: list[str] = []
    for line, mask in zip(lines, mask_lines, strict=True):
        if mask.startswith('import '):
            imports.update(mask[7:].split())
        elif mask.startswith('#print axioms '):
            # Diagnostic output is requested by the validation driver.
            continue
        else:
            result.append(line)
    return '\n'.join(result) + '\n', imports


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path('submission/gram-defect-20261014/proof/Solution.lean'))
    parser.add_argument('--report', type=Path,
                        help='Optional UTF-8/LF provenance report path within the repository')
    args = parser.parse_args()
    output = (root / args.output).resolve()
    if not output.is_relative_to(root):
        parser.error('Output must stay within this repository')
    report_path = (root / args.report).resolve() if args.report else None
    if report_path is not None and not report_path.is_relative_to(root):
        parser.error('Report must stay within this repository')
    names = ['Core', 'ScaledCertificate', 'SharpWindow', 'RefinedCounting', 'Final']
    sources = {name: (root / 'GramDefectRecord' / (name + '.lean')).read_text(encoding='utf-8-sig')
               for name in names}
    core = sources['Core']
    if core.count(BEGIN) != 1 or core.count(END) != 1:
        raise ValueError('Certificate replacement markers are not unique')
    a = core.index(BEGIN)
    z = core.index(END, a) + len(END)
    # These helpers were nested between the old instance and data modules;
    # ScaledCertificate intentionally imports them from Core instead.
    old_block = core[a:z]
    if old_block.count(HELPER_START) != 1:
        raise ValueError('PCell helper start is not unique')
    ha = old_block.index(HELPER_START)
    hz = old_block.index(HELPER_END, ha) + len(HELPER_END)
    helpers = old_block[ha:hz]
    if remaining_sections(helpers) != 0:
        raise ValueError('PCell helper block is not self-contained')
    scaled, scaled_imports = strip_imports(sources['ScaledCertificate'])
    if remaining_sections(scaled) != 0:
        raise ValueError('ScaledCertificate requires unexpected implicit scopes')
    replacement = ('/- The old finite instance, data, full certificate and W9 bridge\n'
                   'are replaced here by the refined, independently checked module.\n'
                   'Shared generic PCell helpers are retained verbatim. -/\n'
                   + helpers + '\n' + scaled)
    modified_core = core[:a] + replacement + core[z:]
    if modified_core[modified_core.index(TRAILER):] != core[core.index(TRAILER):]:
        raise ValueError('The complete upstream license trailer changed')
    if re.search(r'\b(?:PC9QB5C|PC9QB5CData|RiemannFail)\b', code_mask(modified_core)):
        raise ValueError('Old literal certificate assembly survives replacement')
    ratio = re.search(r'^def recordRatio : ℝ := (\d+) / (\d+)$', sources['Final'], re.M)
    if ratio is None:
        raise ValueError('Cannot read the exact submitted fraction from Final')
    p, q = map(int, ratio.groups())
    imports = {'ChallengeDeps.CandidateSpec'}
    metadata: list[dict[str, object]] = []
    payloads: list[str] = []
    for index, name in enumerate(['Core', 'SharpWindow', 'RefinedCounting', 'Final']):
        source = modified_core if name == 'Core' else sources[name]
        body, found_imports = strip_imports(source)
        imports.update(found_imports)
        closed = remaining_sections(body)
        section = f'GramDefectBundleModule_{index}'
        payloads.append('/- Source module: GramDefectRecord/' + name + '.lean -/\n'
                        + f'section {section}\n' + body + '\n'
                        + 'end\n' * closed + f'end {section}\n')
        metadata.append({'path': 'GramDefectRecord/' + name + '.lean',
                         'implicit_sections_closed': closed})
    imports.update(scaled_imports)
    imports = {name for name in imports if not name.startswith('GramDefectRecord.')}
    if any(name.startswith('RecordProportion.') for name in imports):
        raise ValueError('Unexpected local proof-module import')
    header = '''/-
Copyright (c) 2026 Li Xiang (lixiang90), modifications. Apache-2.0.
Derived from the accepted master-of-puppets4 proof by R. Arun Chandru;
upstream attribution and complete third-party notices/licenses remain below.
Modified on 2026-10-14: replace the old finite nine-point certificate by its
scaled rational refinement, retain generic PCell helpers, sharpen the window
floor and expose the three fixed website theorem declarations at root scope.
Generated by scripts/bundle_gram_defect_solution.py, using ordinary Lean
numerals without compression macros. UTF-8, LF. This file needs only the
pinned trusted challenge/Mathlib/Zeta23 imports, not repository proof modules.
The website generates currentRecordKappa and candidateKappa from form inputs.
-/
'''
    wrapper = '''
noncomputable section

/- The trusted website counting functions are independent definition copies.
These reflexive identities preserve the exact zero sets and multiplicities. -/
namespace GramDefectSubmissionCounts

theorem count_eq (T₁ T₂ : ℝ) :
    _root_.Ncount T₁ T₂ = Zeta23.Ncount T₁ T₂ := by rfl

theorem distinct_eq (T₁ T₂ : ℝ) :
    _root_.N0star T₁ T₂ = Zeta23.N0star T₁ T₂ := by rfl

end GramDefectSubmissionCounts

/-- The submitted bound strictly improves the website's trusted current record. -/
theorem candidate_strict_improvement :
    currentRecordKappa < candidateKappa := by
  norm_num [currentRecordKappa, candidateKappa]

/-- The exact submitted fraction bounds distinct critical-line zeros in dyadic windows. -/
theorem candidate_critical_line_bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) := by
  simpa only [candidateKappa, GramDefectRecord.recordRatio,
    GramDefectSubmissionCounts.count_eq, GramDefectSubmissionCounts.distinct_eq] using
    GramDefectRecord.distinct_dyadic

/-- The same exact bound holds in cumulative windows. -/
theorem candidate_critical_line_bound_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T := by
  simpa only [candidateKappa, GramDefectRecord.recordRatio,
    GramDefectSubmissionCounts.count_eq, GramDefectSubmissionCounts.distinct_eq] using
    GramDefectRecord.distinct_cumulative

end
'''
    result = header + ''.join(f'import {name}\n' for name in sorted(imports)) + '\n' + '\n'.join(payloads) + wrapper
    if remaining_sections(result) != 0:
        raise ValueError('Generated bundle scopes are not fully closed')
    mask = code_mask(result)
    for forbidden in ['axiom', 'sorry', 'admit', 'native_decide']:
        if re.search(r'\b' + forbidden + r'\b', mask):
            raise ValueError('Forbidden proof command: ' + forbidden)
    for declaration in ['candidateKappa', 'currentRecordKappa']:
        if re.search(r'\b(?:def|abbrev|opaque|axiom)\s+' + declaration + r'\b', mask):
            raise ValueError('Bundle defines a trusted score: ' + declaration)
    data = result.encode('utf-8')
    if len(data) >= MAX_BYTES:
        raise ValueError(f'Bundle is {len(data)} bytes, exceeding the strict < {MAX_BYTES} limit')
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(data)
    report = {'path': output.relative_to(root).as_posix(), 'bytes': len(data),
              'strict_limit_bytes': MAX_BYTES, 'sha256': hashlib.sha256(data).hexdigest(),
              'numerator': str(p), 'denominator': str(q), 'imports': sorted(imports),
              'modules': metadata, 'scaled_module_implicit_sections_closed': 0,
              'sources_lf_sha256': {name: hashlib.sha256(sources[name].encode()).hexdigest() for name in names},
              'sources_raw_sha256': {name: hashlib.sha256((root / 'GramDefectRecord' / (name + '.lean')).read_bytes()).hexdigest()
                                     for name in names},
              'upstream_trailer_preserved': True, 'proof_verification': 'separate'}
    report_text = json.dumps(report, ensure_ascii=False, indent=2) + '\n'
    if report_path is not None:
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_bytes(report_text.encode('utf-8'))
    print(report_text, end='')


if __name__ == '__main__':
    main()
