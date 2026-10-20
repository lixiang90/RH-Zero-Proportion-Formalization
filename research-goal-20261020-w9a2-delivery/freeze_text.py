"""Freeze exact source text and generate a single-file candidate; never run Lean.

No subprocess, network, installer, optimizer or executable proof evaluator is
used. Each destination is created exclusively. Old source snapshots survive
ordinary-compiler repairs as separate versions, with no overwrite or resume.
"""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
MODULES = [(f'StructuralW9A220261020.{name}',
            f'StructuralW9A220261020/{name}.lean')
           for name in ['Core', 'Graph', 'Localization', 'Counting', 'Final']]
ROOTS = ['candidate_strict_improvement', 'candidate_critical_line_bound',
         'candidate_critical_line_bound_cumulative']
NUMERATOR = '3337881639516708570682858853672166187793'
DENOMINATOR = '4955348542279967171490000000000000000000'
BASE_DENOMINATOR = '4955348548503844558750000000000000000000'
EXPECTED_LEADERBOARD_SHA = 'c774017da684e8721342c256967c96c8f285647893b27253c36ff867922937e6'
IMPORT = re.compile(rb'import ([A-Za-z_][A-Za-z0-9_.]*)\r?\n?\Z')
HEADER = b'''/-
SPDX-License-Identifier: Apache-2.0
PREPARATION ONLY. Frozen W9A2 quantitative localization and finite-state
average-energy candidate. All non-import bytes and inherited notices survive.
Ordinary Lean, exact Comparator comparison, default kernel replay, nanoda,
the complete 3200s production budget and website acceptance remain unproved.
-/
'''


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read(path):
    data = Path(path).read_bytes()
    data.decode('utf-8', errors='strict')
    assert not data.startswith(b'\xef\xbb\xbf'), str(path)
    return data


def write(path, data):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    with Path(path).open('xb') as stream:
        stream.write(data)


def jbytes(obj):
    return (json.dumps(obj, ensure_ascii=False, indent=2) + '\n').encode('utf-8')


def partition(data, module):
    imports, body = [], []
    for line in data.splitlines(keepends=True):
        if line.startswith(b'import '):
            match = IMPORT.fullmatch(line)
            assert match is not None, (module, 'unsupported import grammar')
            imports.append((match[1].decode('ascii'), line))
        else:
            body.append(line)
    result = b''.join(body)
    assert len(data) == len(result) + sum(len(line) for _, line in imports)
    return imports, result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--freeze-once', required=True, action='store_true')
    ap.add_argument('--version', required=True)
    args = ap.parse_args()
    assert re.fullmatch(r'draft-v[0-9]+', args.version)
    dest = HERE / args.version
    assert not dest.exists(), 'Exclusive version already exists; do not overwrite it'
    blobs = {name: read(ROOT/name) for _, name in MODULES}
    wrapper = read(HERE/'public-wrapper.lean.txt')
    ledger = read(ROOT/'research-goal-20261020-w9a2-runtime/leaderboard.json')
    assert sha(ledger) == EXPECTED_LEADERBOARD_SHA
    fresh_receipt = read(ROOT/'research-goal-20261020-w9a2-runtime/leaderboard-receipt.json')
    assert json.loads(fresh_receipt)['sha256'] == sha(ledger)
    records = [r for r in json.loads(ledger)['records']
               if r['track'] == 'critical-line' and r['status'] == 'kernel-verified'
               and r['exactRational'] is not None]
    rational = lambda row: Fraction(int(row['exactRational']['numerator']),
                                    int(row['exactRational']['denominator']))
    current = max(records, key=rational)
    assert current['exactRational'] == {'numerator': NUMERATOR, 'denominator': BASE_DENOMINATOR}
    assert 0 < rational(current) < Fraction(int(NUMERATOR), int(DENOMINATOR)) <= 1
    template_dir = ROOT/'research-20261016-w10-cert/website-snapshot/challenge/templates'
    spec_template = read(template_dir/'CandidateSpec.lean.tmpl')
    challenge_template = read(template_dir/'Challenge.Candidate.lean')
    for token in [b'{{CURRENT_EXPRESSION}}', b'{{NUMERATOR}}', b'{{DENOMINATOR}}']:
        assert spec_template.count(token) == 1
    spec = spec_template.replace(b'{{CURRENT_EXPRESSION}}', current['exactExpression'].encode())
    spec = spec.replace(b'{{NUMERATOR}}', NUMERATOR.encode()).replace(b'{{DENOMINATOR}}', DENOMINATOR.encode())
    assert b'{{' not in spec
    dependencies = read(ROOT/'research-goal-20261020-w9a2-runtime/trusted/ChallengeDeps.lean')
    assert sha(dependencies) == 'f05666d0745edbf2dac6ce2a4de675abd1bba3c336fe24aebb80f27d1365ebbd'
    names = [module for module, _ in MODULES]
    external = []
    parts, moves, sources = [], [], []
    for module, name in MODULES:
        imports, body = partition(blobs[name], module)
        for target, raw in imports:
            internal = target in names
            if internal:
                assert names.index(target) < names.index(module), (module, target)
            else:
                external.append(raw)
            moves.append({'source': name, 'import': target, 'internal': internal,
                          'removed_line_bytes': len(raw), 'removed_line_sha256': sha(raw)})
        parts.append((module, body))
        sources.append({'module': module, 'path': name, 'bytes': len(blobs[name]),
                        'sha256': sha(blobs[name]), 'retained_non_import_bytes': len(body),
                        'retained_non_import_sha256': sha(body)})
    assert b'import ChallengeDeps.CandidateSpec\n' not in external
    result = HEADER + b'import ChallengeDeps.CandidateSpec\n' + b''.join(external) + b'\n'
    segments = []
    for module, body in parts:
        result += ('\n/- BEGIN FLATTENED MODULE ' + module + ' -/\n').encode()
        start = len(result)
        result += body
        segments.append({'module': module, 'start': start, 'end': len(result),
                         'retained_non_import_sha256': sha(body)})
        assert result[start:len(result)] == body
        result += b'\n'
    result += b'\n' + wrapper
    assert len(result) <= 2_000_000, ('Complete source exceeds website budget', len(result))
    assert b'import StructuralW9A220261020.' not in result
    assert not re.search(rb'(?m)^\s*(?:noncomputable\s+)?def\s+(?:candidateKappa|currentRecordKappa)\b', result)
    for name in ROOTS:
        assert len(re.findall(rb'(?m)^theorem ' + name.encode() + rb'\s*:', result)) == 1, name
    score = Fraction(int(NUMERATOR), int(DENOMINATOR))
    with localcontext() as context:
        context.prec = 65
        display = str(100*Decimal(score.numerator)/Decimal(score.denominator))
        delta = score-rational(current)
        improvement = str(100*Decimal(delta.numerator)/Decimal(delta.denominator))
    plan = {'schema': 'w9a2-text-delivery-v1', 'upload_ready': False,
            'scope': 'Text preparation only; no Lean/export/Comparator/kernel/optimizer execution',
            'score': {'numerator': NUMERATOR, 'denominator': DENOMINATOR},
            'score_percent_display_only': display,
            'increment_percentage_points_display_only': improvement,
            'current_record': current,
            'fresh_record_receipt_utc': json.loads(fresh_receipt)['retrievedAt'],
            'record_freshness_at_future_execution_must_be_rechecked': True,
            'solution_bytes': len(result), 'solution_sha256': sha(result),
            'website_source_limit_bytes': 2_000_000, 'source_slack_bytes': 2_000_000-len(result),
            'source_modules': sources, 'body_segments': segments, 'import_lines_moved': moves,
            'external_import_lines_preserved': [r.decode().strip() for r in external],
            'additional_trusted_import': 'ChallengeDeps.CandidateSpec',
            'all_non_import_bytes_preserved': True,
            'public_roots': ROOTS, 'all_non_text_proof_runs': 0,
            'complete_3200s_passed': False, 'official_accepted': False}
    dest.mkdir()
    write(dest/'Solution.lean', result)
    for _, name in MODULES:
        write(dest/'frozen-inputs'/name, blobs[name])
    write(dest/'frozen-inputs/public-wrapper.lean.txt', wrapper)
    write(dest/'frozen-inputs/CandidateSpec.lean.tmpl', spec_template)
    write(dest/'frozen-inputs/Challenge.Candidate.lean', challenge_template)
    write(dest/'frozen-inputs/leaderboard.json', ledger)
    write(dest/'frozen-inputs/leaderboard-receipt.json', fresh_receipt)
    write(dest/'trusted/ChallengeDeps.lean', dependencies)
    write(dest/'trusted/ChallengeDeps/CandidateSpec.lean', spec)
    write(dest/'trusted/Challenge/Candidate.lean', challenge_template)
    write(dest/'candidate-parameters.json', jbytes(plan))
    # The live originals are checked again after exclusive output writes.
    for _, name in MODULES:
        assert read(ROOT/name) == blobs[name], ('Source changed during snapshot', name)
    files = [{'path': p.relative_to(dest).as_posix(), 'bytes': p.stat().st_size,
              'sha256': sha(p.read_bytes())} for p in sorted(dest.rglob('*')) if p.is_file()]
    write(dest/'files.json', jbytes({'scope': 'Unverified source preparation only', 'files': files}))
    print(json.dumps({'version': args.version, 'solution_bytes': len(result),
                      'solution_sha256': sha(result), 'upload_ready': False,
                      'manifest_sha256': sha((dest/'files.json').read_bytes())}))


if __name__ == '__main__':
    main()
