"""Exclusive, deterministic source concatenation only; never invokes Lean.

This script is PREPARATION and is not executed by preparing its manifest.
A future explicitly authorized invocation creates draft/Solution.lean and
metadata, marked upload_ready=False. It never writes trusted dependencies.
"""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PREPARED = HERE / 'prepared-files.json'
PINS = HERE / 'input-pins.json'
PLAN = HERE / 'candidate-parameters.json'
WRAPPER = HERE / 'official-wrapper.lean.txt'
DEST = HERE / 'draft'
MODULES = (
    ('StructuralS1RTiny20261018.Production.Core', 'StructuralS1RTiny20261018/Production/Core.lean'),
    ('StructuralS1RTiny20261018.Production.Localization', 'StructuralS1RTiny20261018/Production/Localization.lean'),
    ('StructuralS1RTiny20261018.Production.Counting', 'StructuralS1RTiny20261018/Production/Counting.lean'),
    ('StructuralS1RTiny20261018.Production.Final', 'StructuralS1RTiny20261018/Production/Final.lean'),
)

IMPORT = re.compile(rb'import ([A-Za-z_][A-Za-z0-9_.]*)\r?\n?\Z')
HEADER = (
    '/-\nSPDX-License-Identifier: Apache-2.0\n'
    'DRAFT, upload_ready=false. Deterministic flattening of pinned tiny s1R modules.\n'
    'All non-import source bytes and all inherited notices/licenses are retained.\n'
    'Fresh trusted CandidateSpec, ordinary kernel, Comparator, export, nanoda,\n'
    'resource and independent source audits remain mandatory.\n-/\n'
).encode('utf-8')

def sha(blob):
    return hashlib.sha256(blob).hexdigest()

def relative(path):
    return path.relative_to(ROOT).as_posix()

def load(path):
    return json.loads(path.read_text(encoding='utf-8'))

def checked(path, expected):
    data = path.read_bytes()
    assert sha(data) == expected, relative(path)
    data.decode('utf-8', errors='strict')
    assert not data.startswith(b'\xef\xbb\xbf'), 'unexpected BOM'
    return data

def partition(data, module):
    """Move only whole-line imports; reject unrecognized import syntax.

    Sources are immutable/pinned. No comment or declaration is discarded.
    A changed source with another import grammar requires a versioned tool.
    """
    imports, body = [], []
    for line in data.splitlines(keepends=True):
        if line.startswith(b'import '):
            match = IMPORT.fullmatch(line)
            assert match is not None, (module, 'unsupported import syntax')
            imports.append((match[1].decode('ascii'), line))
        else:
            body.append(line)
    result = b''.join(body)
    assert len(data) == len(result) + sum(len(line) for _, line in imports)
    return imports, result

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--generate-draft-once', action='store_true', required=True)
    parser.add_argument('--prepared-sha256', required=True)
    args = parser.parse_args()
    assert sha(PREPARED.read_bytes()) == args.prepared_sha256
    prep = load(PREPARED)
    runtime = prep['external_runtime_identity']
    assert sha(Path(sys.executable).read_bytes()) == runtime['sha256']
    assert sys.version == runtime['version']
    # Lock the executable, wrapper, parameter plan and every read dependency.
    allpins = {row['path']: row['sha256'] for row in prep['files']}
    allpins.update({row['path']: row['sha256'] for row in prep['read_dependencies']})
    for name, expected in allpins.items():
        checked(ROOT / name, expected)
    inputs = load(PINS)
    plan = load(PLAN)
    assert plan['upload_ready'] is False
    assert plan['trusted_CandidateSpec_written_or_modified'] is False
    assert not DEST.exists(), 'exclusive output directory already exists'
    own_names = {module for module, _ in MODULES}
    imported = []
    parts = []
    removals = []
    dependencies = []
    for module, name in MODULES:
        data = checked(ROOT / name, inputs['module_sha256'][name])
        lines, body = partition(data, module)
        parts.append((module, body))
        for target, raw in lines:
            removals.append({'source': name, 'module': target,
                             'import_line_sha256': sha(raw),
                             'internal': target in own_names})
            if target in own_names:
                assert [m for m, _ in MODULES].index(target) < [m for m, _ in MODULES].index(module)
            else:
                assert target in inputs['external_imports'], target
                imported.append(raw)
        dependencies.append({'path': name, 'sha256': sha(data), 'bytes': len(data),
                             'retained_non_import_sha256': sha(body),
                             'retained_non_import_bytes': len(body)})
    assert [line.decode('ascii').strip()[7:] for line in imported] == inputs['external_imports']
    # Existing external imports retain their exact bytes/order at the header.
    result = HEADER + b''.join(imported) + b'\n'
    offsets = []
    for module, body in parts:
        separator = ('\n/- BEGIN FLATTENED MODULE ' + module + ' -/\n').encode('ascii')
        result += separator
        start = len(result)
        result += body
        end = len(result)
        assert result[start:end] == body
        offsets.append({'module': module, 'start': start, 'end': end,
                        'non_import_sha256': sha(body)})
        result += b'\n'
    wrapper = checked(WRAPPER, allpins[relative(WRAPPER)])
    result += b'\n' + wrapper
    assert len(result) <= 2_000_000, ('source budget exceeded', len(result))
    assert b'import StructuralS1R' not in result
    assert not re.search(rb'(?m)^\s*(?:noncomputable\s+)?def\s+(?:currentRecordKappa|candidateKappa)\b', result)
    # The old public wrappers must be absent from all input module bodies.
    for name in ('candidate_strict_improvement', 'candidate_critical_line_bound',
                 'candidate_critical_line_bound_cumulative'):
        assert len(re.findall(rb'(?m)^theorem ' + name.encode() + rb'\s*:', result)) == 1, name
    metadata = dict(plan)
    metadata.update({'schema': 'tiny-source-draft-v1',
                     'solution': 'Solution.lean', 'solution_bytes': len(result),
                     'solution_sha256': sha(result),
                     'prepared_manifest_sha256': args.prepared_sha256,
                     'source_modules': dependencies,
                     'body_segments': offsets, 'imports_moved': removals,
                     'all_non_import_bytes_preserved': True,
                     'compiler_inputs_modified': False,
                     'production_runs': 0, 'Lean_runs': 0,
                     'Comparator_runs': 0, 'Nano_runs': 0})
    manifest = {'scope': 'Unverified draft source only', 'upload_ready': False,
                'files': [{'path': 'Solution.lean', 'bytes': len(result), 'sha256': sha(result)}]}
    # Exclusive creation never overwrites an earlier attempt; failures retain it.
    DEST.mkdir()
    with (DEST / 'Solution.lean').open('xb') as handle:
        handle.write(result)
    raw_metadata = (json.dumps(metadata, ensure_ascii=False, indent=2) + '\n').encode()
    with (DEST / 'candidate-metadata.json').open('xb') as handle:
        handle.write(raw_metadata)
    manifest['files'].append({'path': 'candidate-metadata.json',
                              'bytes': len(raw_metadata), 'sha256': sha(raw_metadata)})
    with (DEST / 'generation.json').open('x', encoding='utf-8', newline='\n') as handle:
        json.dump(manifest, handle, ensure_ascii=False, indent=2)
        handle.write('\n')
    # Verify every frozen input once more without touching its bytes.
    for name, expected in allpins.items():
        checked(ROOT / name, expected)
    print(json.dumps({'draft_written': True, 'upload_ready': False,
                      'solution_bytes': len(result), 'solution_sha256': sha(result)}))

if __name__ == '__main__':
    main()
