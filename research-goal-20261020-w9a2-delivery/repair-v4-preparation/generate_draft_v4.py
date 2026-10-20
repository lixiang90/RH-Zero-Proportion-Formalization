"""Exclusive text-only draft-v4 from frozen draft-v3 plus sealed Localization proof repair.

No compiler, exporter, kernel, solver, subprocess or network call.
"""
import argparse
import ast
import copy
import difflib
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parent
PRIOR = HERE / 'draft-v3'
REPAIR = ROOT / 'research-goal-20261020-w9a2-localization-repair-v1'
PRIOR_MANIFEST_SHA = '6440e71dd49ef31704f2c331d03af83abfd8bf9eabeca54c479bac44e755c8cb'
REPAIR_MANIFEST_SHA = 'e68e29c644e019de387e8570db5c86c9af80cc9fc9a13224e928c6e3d2f1fd31'
MODULE_PATH = 'StructuralW9A220261020/Localization.lean'
OLD = b'      simpa only [reverse8] using (le_of_lt (lt_of_not_ge ho))\n'
NEW = '      change g 7 ≤ g 0\n      exact le_of_lt (lt_of_not_ge ho)\n'.encode()
IMPORT = re.compile(rb'import ([A-Za-z_][A-Za-z0-9_.]*)\r?\n?\Z')


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read(path):
    raw = path.read_bytes(); raw.decode('utf-8', errors='strict')
    assert not raw.startswith(b'\xef\xbb\xbf')
    return raw


def dump(obj):
    return (json.dumps(obj, ensure_ascii=False, indent=2) + '\n').encode()


def write(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as stream:
        stream.write(raw)


def row(path, base):
    raw = read(path)
    return {'path': path.relative_to(base).as_posix(), 'bytes': len(raw), 'sha256': sha(raw)}


def manifest(path, expected):
    raw = read(path); assert sha(raw) == expected
    data = json.loads(raw)
    for entry in data['files']:
        item = (path.parent / entry['path']).resolve()
        assert item.is_relative_to(path.parent.resolve())
        actual = read(item)
        assert len(actual) == entry['bytes'] and sha(actual) == entry['sha256']
    return data


def literal(path, name):
    values = [node.value for node in ast.parse(read(path)).body if isinstance(node, ast.Assign)
        and any(isinstance(t, ast.Name) and t.id == name for t in node.targets)]
    assert len(values) == 1
    return ast.literal_eval(values[0])


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--freeze-once', action='store_true', required=True)
    ap.parse_args()
    dest = HERE / 'draft-v4'; assert not dest.exists()
    prior_manifest = manifest(PRIOR / 'files.json', PRIOR_MANIFEST_SHA)
    repair_manifest = manifest(REPAIR / 'files.json', REPAIR_MANIFEST_SHA)
    plan = copy.deepcopy(json.loads(read(PRIOR / 'candidate-parameters.json')))
    original = read(PRIOR / 'frozen-inputs' / MODULE_PATH)
    repaired = read(REPAIR / MODULE_PATH)
    canonical_v0 = read(ROOT / MODULE_PATH)
    assert sha(canonical_v0) == '95138259450a504e9db184baa3b1e3b5cd1bdb8e11c8990d4b20a94cc7643a2d'
    assert original.count(OLD) == repaired.count(NEW) == 1
    assert NEW not in original and OLD not in repaired
    assert original.replace(OLD, NEW) == repaired and repaired.replace(NEW, OLD) == original
    assert len(repaired) == 13295 and len(repaired) - len(original) == 1
    assert sha(repaired) == 'f4d32498996dd5f2781cdac1b17531c02757467dc62fae4e5b88d7d675842fd4'
    oldlines, newlines = original.splitlines(keepends=True), repaired.splitlines(keepends=True)
    assert len(newlines) == len(oldlines) + 1
    assert oldlines[261] == OLD and b''.join(newlines[261:263]) == NEW
    assert oldlines[:261] == newlines[:261] and oldlines[262:] == newlines[263:]
    hor = '    have hor : reverse8 g 0 ≤ reverse8 g 7 := by\n'.encode()
    assert original.count(hor) == repaired.count(hor) == 1
    marker = b'theorem located_state '
    def theorem(raw):
        assert raw.count(marker) == 1
        a = raw.index(marker); b = raw.index(b':= by', a)
        return raw[a:b]
    assert theorem(original) == theorem(repaired)
    header = literal(HERE / 'freeze_text.py', 'HEADER')
    runner = ROOT / 'research-goal-20261020-w9a2-verification-preparation-v1/run_verification.py'
    assert sha(read(runner)) == '92cc8dcf3e3c46e76490ba7bfe8d93bc10e331131eaab3b4c3ae500f80ac66a8'
    assert literal(runner, 'HEADER') == header
    names = [entry['module'] for entry in plan['source_modules']]
    imports, parts, sources, origins = [], [], [], []
    for entry in plan['source_modules']:
        path, module = entry['path'], entry['module']
        source = REPAIR / path if path == MODULE_PATH else PRIOR / 'frozen-inputs' / path
        raw = read(source); body = []
        for line in raw.splitlines(keepends=True):
            if line.startswith(b'import '):
                match = IMPORT.fullmatch(line); assert match is not None
                name = match[1].decode()
                if name in names:
                    assert names.index(name) < names.index(module)
                else:
                    imports.append(line)
            else:
                body.append(line)
        retained = b''.join(body)
        parts.append((module, retained))
        sources.append({'module': module, 'path': path, 'bytes': len(raw), 'sha256': sha(raw),
            'retained_non_import_bytes': len(retained), 'retained_non_import_sha256': sha(retained)})
        origins.append({'logical_path': path, 'actual_input': row(source, ROOT)})
    result = header + b'import ChallengeDeps.CandidateSpec\n' + b''.join(imports) + b'\n'
    segments = []
    for module, body in parts:
        result += ('\n/- BEGIN FLATTENED MODULE ' + module + ' -/\n').encode()
        a = len(result); result += body
        segments.append({'module': module, 'start': a, 'end': len(result),
            'retained_non_import_sha256': sha(body)})
        result += b'\n'
    wrapper = read(PRIOR / 'frozen-inputs/public-wrapper.lean.txt')
    result += b'\n' + wrapper
    prior = read(PRIOR / 'Solution.lean')
    assert prior.count(OLD) == result.count(NEW) == 1
    assert prior.replace(OLD, NEW) == result and result.replace(NEW, OLD) == prior
    assert len(result) == 1829994 and len(result) <= 2000000
    types = []
    official = read(PRIOR / 'frozen-inputs/Challenge.Candidate.lean')
    for name in plan['public_roots']:
        pattern = rb'(?ms)^theorem ' + name.encode() + rb'\s*:\s*(.*?)\s*:= by'
        actual, expected = re.findall(pattern, wrapper), re.findall(pattern, official)
        assert len(actual) == len(expected) == 1 and b''.join(actual[0].split()) == b''.join(expected[0].split())
        types.append({'name': name, 'type_sha256': sha(actual[0]), 'unchanged_and_official_mod_whitespace': True})
    plan.update(solution_bytes=len(result), solution_sha256=sha(result), source_slack_bytes=2000000-len(result),
        source_modules=sources, body_segments=segments, source_revision='draft-v4-definitional-reflected-endpoint-in-Localization-proof',
        repair_manifest_sha256=REPAIR_MANIFEST_SHA, previous_draft_manifest_sha256=PRIOR_MANIFEST_SHA)
    review = {'scope': 'Independent byte-only delivery review; no semantic/proof execution',
        'repair_manifest_rows_verified': len(repair_manifest['files']),
        'previous_draft_manifest_rows_verified': len(prior_manifest['files']),
        'theorem': 'StructuralW9A220261020.Localization.located_state', 'theorem_statement_sha256': sha(theorem(original)),
        'same_theorem_statement': True, 'changed_Localization_line': 262, 'byte_delta': 1,
        'old_line': OLD.decode().rstrip('\r\n'), 'new_line': NEW.decode().rstrip('\r\n'),
        'Localization_forward_and_reverse_projection_exact': True,
        'all_bytes_outside_single_proof_line_unchanged': True,
        'all_definitions_data_exterior_reflection_coverage_StateAt_cost_threshold_bytes_unchanged': True,
        'four_other_modules_and_whole_wrapper_from_frozen_draft_v3_byte_identical': True,
        'single_file_forward_and_reverse_projection_exact': True, 'public_statement_types': types,
        'trusted_inputs_byte_identical_to_frozen_draft_v3': True,
        'canonical_Localization_v0_unchanged': True, 'all_previous_drafts_and_manifests_preserved': True,
        'proof_compiler_export_kernel_search_runs': 0, 'ordinary_Localization_pass_claimed': False,
        'Comparator_passed': False, 'independent_kernels_passed': False, 'complete_3200s_passed': False,
        'official_accepted': False, 'main_round_counter_changed': False}
    dest.mkdir()
    for folder in ['frozen-inputs', 'trusted']:
        for source in sorted((PRIOR / folder).rglob('*')):
            if source.is_file():
                relative = source.relative_to(PRIOR).as_posix()
                write(dest / relative, repaired if relative == 'frozen-inputs/' + MODULE_PATH else read(source))
    write(dest / 'Solution.lean', result)
    write(dest / 'candidate-parameters.json', dump(plan))
    write(dest / 'source-review.json', dump(review))
    write(dest / 'source-origins.json', dump({'scope': 'Text source bindings only', 'module_inputs': origins,
        'previous_draft_manifest': row(PRIOR / 'files.json', ROOT),
        'Localization_repair_manifest': row(REPAIR / 'files.json', ROOT),
        'wrapper': row(PRIOR / 'frozen-inputs/public-wrapper.lean.txt', ROOT)}))
    diff = ''.join(difflib.unified_diff(prior.decode().splitlines(keepends=True),
        result.decode().splitlines(keepends=True), fromfile='draft-v3/Solution.lean', tofile='draft-v4/Solution.lean'))
    write(dest / 'Solution-v3-to-v4.diff', diff.encode())
    manifest(PRIOR / 'files.json', PRIOR_MANIFEST_SHA)
    manifest(REPAIR / 'files.json', REPAIR_MANIFEST_SHA)
    assert read(ROOT / MODULE_PATH) == canonical_v0
    files = [row(p, dest) for p in sorted(dest.rglob('*')) if p.is_file()]
    write(dest / 'files.json', dump({'scope': 'Unverified source preparation only', 'files': files}))
    print(json.dumps({'version': 'draft-v4', 'solution_bytes': len(result), 'solution_sha256': sha(result),
        'manifest_sha256': sha(read(dest / 'files.json')), 'source_slack_bytes': 2000000-len(result),
        'upload_ready': False, 'proof_compiler_export_kernel_search_runs': 0}))


if __name__ == '__main__':
    main()
