"""Pure byte review and exclusive flattening of the one-line Core repair.

No imported preparation module, subprocess, network, compiler, exporter, solver,
or kernel is executed. Frozen v0 and the sealed repair are inputs only.
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
V0 = HERE / 'draft-v0'
REPAIR = ROOT / 'research-goal-20261020-w9a2-core-repair-v1'
EXPECTED_V0_MANIFEST = '71dce9f3714334dd1f525f037f18ee1c6a4ba25a2b3ac9838df49cc6934879f7'
EXPECTED_DELIVERY_MANIFEST = '026672c0c1203d0ac12b44ceadc9cb740f5cc1ef2e7ffc93284b6fb2b4ed5ce0'
EXPECTED_REPAIR_MANIFEST = '9aafa909450a60295a0864982d8f3f596217fba54c8e04eeeb3a21eede8f5114'
OLD = '      simpa only [qTargetFrom, hs, ↓reduceIte] using h\n'.encode()
NEW = '      simpa only [qTargetFrom, hs, Bool.false_eq_true, ↓reduceIte] using h\n'.encode()
MODULES = [(f'StructuralW9A220261020.{name}', f'StructuralW9A220261020/{name}.lean')
           for name in ['Core', 'Graph', 'Localization', 'Counting', 'Final']]
ROOTS = ['candidate_strict_improvement', 'candidate_critical_line_bound',
         'candidate_critical_line_bound_cumulative']
IMPORT = re.compile(rb'import ([A-Za-z_][A-Za-z0-9_.]*)\r?\n?\Z')


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read(path):
    raw = path.read_bytes()
    raw.decode('utf-8', errors='strict')
    assert not raw.startswith(b'\xef\xbb\xbf'), path
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


def check_manifest(path, digest):
    raw = read(path)
    assert sha(raw) == digest, path
    manifest = json.loads(raw)
    for entry in manifest['files']:
        target = (path.parent / entry['path']).resolve()
        assert target.is_relative_to(path.parent.resolve()), target
        actual = read(target)
        assert len(actual) == entry['bytes'] and sha(actual) == entry['sha256'], target
    return manifest


def literal_assignment(path, name):
    tree = ast.parse(read(path).decode(), filename=str(path))
    expressions = [item.value for item in tree.body if isinstance(item, ast.Assign)
                   and any(isinstance(t, ast.Name) and t.id == name for t in item.targets)]
    assert len(expressions) == 1
    return ast.literal_eval(expressions[0])


def partition(raw):
    imports, body = [], []
    for line in raw.splitlines(keepends=True):
        if line.startswith(b'import '):
            match = IMPORT.fullmatch(line)
            assert match is not None
            imports.append((match[1].decode('ascii'), line))
        else:
            body.append(line)
    return imports, b''.join(body)


def statement(raw, name):
    matches = re.findall(rb'(?ms)^theorem ' + name.encode() + rb'\s*:\s*(.*?)\s*:= by', raw)
    assert len(matches) == 1, name
    return matches[0]


def between(raw, first, last):
    assert raw.count(first) == raw.count(last) == 1
    a, b = raw.index(first), raw.index(last)
    assert a < b
    return raw[a:b + len(last)]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--freeze-once', required=True, action='store_true')
    args = ap.parse_args()
    dest = HERE / 'draft-v1'
    assert not dest.exists(), 'Never overwrite a frozen draft'
    check_manifest(HERE / 'prepared-files.json', EXPECTED_DELIVERY_MANIFEST)
    check_manifest(V0 / 'files.json', EXPECTED_V0_MANIFEST)
    check_manifest(REPAIR / 'files.json', EXPECTED_REPAIR_MANIFEST)
    original = {path: read(V0 / 'frozen-inputs' / path) for _, path in MODULES}
    repaired = read(REPAIR / 'canonical-full/StructuralW9A220261020/Core.lean')
    core_path = MODULES[0][1]
    oldcore = original[core_path]
    assert read(ROOT / core_path) == oldcore
    assert oldcore.count(OLD) == repaired.count(NEW) == 1
    assert NEW not in oldcore and OLD not in repaired
    assert oldcore.replace(OLD, NEW) == repaired
    assert repaired.replace(NEW, OLD) == oldcore
    assert len(repaired) - len(oldcore) == 20
    assert sha(repaired) == 'c2af225175f9a5ab14d2ba2612714a21e0613f66107a1d75b9d47bf1c77ba02a'
    before, after = oldcore.splitlines(keepends=True), repaired.splitlines(keepends=True)
    assert len(before) == len(after)
    changes = [(i + 1, a, b) for i, (a, b) in enumerate(zip(before, after)) if a != b]
    assert changes == [(10752, OLD, NEW)]
    theorem0 = between(oldcore, b'theorem qTargetFrom_sound ', b':= by\n  induction ks with')
    theorem1 = between(repaired, b'theorem qTargetFrom_sound ', b':= by\n  induction ks with')
    assert theorem0 == theorem1
    data0 = between(oldcore, b'namespace AMW.Cert.PC9QB6MData\n', b'end AMW.Cert.PC9QB6MData\n')
    data1 = between(repaired, b'namespace AMW.Cert.PC9QB6MData\n', b'end AMW.Cert.PC9QB6MData\n')
    assert data0 == data1
    bool_path = ROOT / 'tmp/lean-toolchain/src/lean/Init/Data/Bool.lean'
    bool_raw = read(bool_path)
    assert sha(bool_raw) == 'ee68370968bd91b779b2f2063bad8701bd5f455b32ea8d503a5234dc3a3cb10a'
    assert b'@[simp] theorem false_eq_true : (false = true) = False := by simp\n' in bool_raw
    split_root = ROOT / 'research-goal-20261020-w9a2-formal-static-review'
    split0 = read(split_root / 'development-split/StructuralW9A220261020/Core.lean')
    split1 = read(REPAIR / 'development-split/StructuralW9A220261020/Core.lean')
    prefix = read(split_root / 'development-split/StructuralW9A220261020/Prefix.lean')
    audit = json.loads(read(split_root / 'split-audit.json'))
    prologue, closing = audit['suffix_prologue'].encode(), audit['prefix_added_closing_command'].encode()
    assert split0.count(OLD) == split1.count(NEW) == 1 and split0.replace(OLD, NEW) == split1
    assert split0.startswith(prologue) and split1.startswith(prologue) and prefix.endswith(closing)
    assert prefix[:-len(closing)] + split0[len(prologue):] == oldcore
    assert prefix[:-len(closing)] + split1[len(prologue):] == repaired
    # Read only literal bytes from the original generator and the frozen runner.
    # Neither module is imported or executed.
    header = literal_assignment(HERE / 'freeze_text.py', 'HEADER')
    runner = ROOT / 'research-goal-20261020-w9a2-verification-preparation-v1/run_verification.py'
    assert sha(read(runner)) == '92cc8dcf3e3c46e76490ba7bfe8d93bc10e331131eaab3b4c3ae500f80ac66a8'
    assert literal_assignment(runner, 'HEADER') == header
    blobs = dict(original)
    blobs[core_path] = repaired
    wrapper = read(V0 / 'frozen-inputs/public-wrapper.lean.txt')
    official = read(V0 / 'frozen-inputs/Challenge.Candidate.lean')
    statement_rows = []
    for name in ROOTS:
        actual, expected = statement(wrapper, name), statement(official, name)
        assert b''.join(actual.split()) == b''.join(expected.split())
        statement_rows.append({'name': name, 'unchanged_wrapper_type_sha256': sha(actual),
                               'official_type_equal_after_whitespace_normalization': True})
    names = [module for module, _ in MODULES]
    imports, parts, moves, sources = [], [], [], []
    for module, path in MODULES:
        incoming, body = partition(blobs[path])
        for target, raw in incoming:
            internal = target in names
            if internal:
                assert names.index(target) < names.index(module)
            else:
                imports.append(raw)
            moves.append({'source': path, 'import': target, 'internal': internal,
                          'removed_line_bytes': len(raw), 'removed_line_sha256': sha(raw)})
        parts.append((module, body))
        sources.append({'module': module, 'path': path, 'bytes': len(blobs[path]),
                        'sha256': sha(blobs[path]), 'retained_non_import_bytes': len(body),
                        'retained_non_import_sha256': sha(body)})
    solution = header + b'import ChallengeDeps.CandidateSpec\n' + b''.join(imports) + b'\n'
    segments = []
    for module, body in parts:
        solution += ('\n/- BEGIN FLATTENED MODULE ' + module + ' -/\n').encode()
        start = len(solution)
        solution += body
        segments.append({'module': module, 'start': start, 'end': len(solution),
                         'retained_non_import_sha256': sha(body)})
        solution += b'\n'
    solution += b'\n' + wrapper
    oldsolution = read(V0 / 'Solution.lean')
    assert oldsolution.count(OLD) == solution.count(NEW) == 1
    assert oldsolution.replace(OLD, NEW) == solution and solution.replace(NEW, OLD) == oldsolution
    assert len(solution) == 1829955 and len(solution) <= 2000000
    plan = copy.deepcopy(json.loads(read(V0 / 'candidate-parameters.json')))
    assert plan['import_lines_moved'] == moves
    plan.update({'solution_bytes': len(solution), 'solution_sha256': sha(solution),
                 'source_slack_bytes': 2000000 - len(solution), 'source_modules': sources,
                 'body_segments': segments,
                 'source_revision': 'draft-v1-one-existing-Bool-simp-rule',
                 'repair_manifest_sha256': EXPECTED_REPAIR_MANIFEST,
                 'previous_draft_manifest_sha256': EXPECTED_V0_MANIFEST})
    origins = {'scope': 'Frozen byte sources, not compilation evidence',
        'repair_manifest': row(REPAIR / 'files.json', ROOT),
        'previous_draft_manifest': row(V0 / 'files.json', ROOT),
        'module_inputs': [{'logical_path': path, 'actual_input': row(
            REPAIR / 'canonical-full' / path if path == core_path else V0 / 'frozen-inputs' / path,
            ROOT)} for _, path in MODULES],
        'wrapper': row(V0 / 'frozen-inputs/public-wrapper.lean.txt', ROOT),
        'header_generator': row(HERE / 'freeze_text.py', ROOT),
        'frozen_verification_runner': row(runner, ROOT),
        'sdk_Bool_source': row(bool_path, ROOT),
        'record_freshness_at_future_execution_must_be_rechecked': True}
    review = {'scope': 'Independent delivery byte review only; no semantic execution',
        'repair_manifest_14_rows_verified': True, 'v0_manifest_15_rows_verified': True,
        'canonical_v0_unchanged': True, 'full_v0_to_v1_only_single_line': True,
        'changed_full_line': 10752, 'old_line': OLD.decode().rstrip('\n'),
        'new_line': NEW.decode().rstrip('\n'), 'byte_delta': 20,
        'theorem': 'AMW.Cert.PC9QB6M.qTargetFrom_sound',
        'theorem_statement_unchanged_sha256': sha(theorem0),
        'entire_Data_namespace_unchanged_bytes': len(data0),
        'entire_Data_namespace_unchanged_sha256': sha(data0),
        'all_other_full_Core_bytes_equal_by_reversible_projection': True,
        'all_walk_payload_cost_threshold_guard_cursor_bytes_unchanged': True,
        'exact_old_prefix_plus_new_suffix_equals_new_full': True,
        'four_companion_modules_byte_identical_to_frozen_v0': True,
        'wrapper_entire_bytes_identical_to_frozen_v0': True,
        'public_statement_types': statement_rows,
        'all_import_moves_identical_to_v0': True,
        'single_file_reverse_projection_equals_exact_v0': True,
        'all_non_import_bytes_preserved': True,
        'trusted_template_spec_challenge_dependencies_byte_identical_to_frozen_v0': True,
        'ordinary_compile_passed': False, 'comparator_passed': False,
        'default_kernel_passed': False, 'nanoda_passed': False,
        'complete_3200s_passed': False, 'official_accepted': False,
        'proof_compiler_export_kernel_search_runs': 0,
        'main_round_counter_changed': False}
    dest.mkdir()
    # Copy every previous non-derived artifact. Only the frozen Core is replaced.
    for entry in json.loads(read(V0 / 'files.json'))['files']:
        relative = entry['path']
        if relative in ['candidate-parameters.json', 'Solution.lean']:
            continue
        raw = repaired if relative == 'frozen-inputs/' + core_path else read(V0 / relative)
        write(dest / relative, raw)
    write(dest / 'Solution.lean', solution)
    write(dest / 'candidate-parameters.json', dump(plan))
    write(dest / 'source-origins.json', dump(origins))
    write(dest / 'source-review.json', dump(review))
    delta = ''.join(difflib.unified_diff(oldsolution.decode().splitlines(keepends=True),
        solution.decode().splitlines(keepends=True), fromfile='draft-v0/Solution.lean',
        tofile='draft-v1/Solution.lean'))
    write(dest / 'Solution-v0-to-v1.diff', delta.encode())
    check_manifest(HERE / 'prepared-files.json', EXPECTED_DELIVERY_MANIFEST)
    check_manifest(V0 / 'files.json', EXPECTED_V0_MANIFEST)
    check_manifest(REPAIR / 'files.json', EXPECTED_REPAIR_MANIFEST)
    assert read(ROOT / core_path) == oldcore
    files = [row(path, dest) for path in sorted(dest.rglob('*')) if path.is_file()]
    write(dest / 'files.json', dump({'scope': 'Unverified source preparation only', 'files': files}))
    print(json.dumps({'version': 'draft-v1', 'solution_bytes': len(solution),
        'solution_sha256': sha(solution), 'manifest_sha256': sha(read(dest / 'files.json')),
        'source_slack_bytes': 2000000 - len(solution), 'upload_ready': False,
        'compiler_export_kernel_search_runs': 0}))


if __name__ == '__main__':
    main()
