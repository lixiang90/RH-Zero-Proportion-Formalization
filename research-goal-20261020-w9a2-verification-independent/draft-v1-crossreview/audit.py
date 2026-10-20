"""Independent text/hash audit only. Never imports a candidate or runner."""
import ast
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent
D = ROOT / 'research-goal-20261020-w9a2-delivery'
V0, V1 = D / 'draft-v0', D / 'draft-v1'
REPAIR = ROOT / 'research-goal-20261020-w9a2-core-repair-v1'
MODULES = ['Core', 'Graph', 'Localization', 'Counting', 'Final']
OLD = '      simpa only [qTargetFrom, hs, ↓reduceIte] using h\n'.encode()
NEW = '      simpa only [qTargetFrom, hs, Bool.false_eq_true, ↓reduceIte] using h\n'.encode()
INPUTS = {}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read(path):
    raw = path.read_bytes()
    key = path.resolve().relative_to(ROOT.resolve()).as_posix()
    prior = INPUTS.setdefault(key, {'bytes': len(raw), 'sha256': sha(raw)})
    assert prior == {'bytes': len(raw), 'sha256': sha(raw)}, key
    return raw


def manifest(path, expected):
    raw = read(path)
    assert sha(raw) == expected, str(path)
    value = json.loads(raw)
    paths = [item['path'] for item in value['files']]
    assert len(paths) == len(set(paths))
    for item in value['files']:
        target = (path.parent / item['path']).resolve()
        assert target.is_relative_to(path.parent.resolve())
        actual = read(target)
        assert len(actual) == item['bytes'] and sha(actual) == item['sha256']
    return value


def literal(path, name):
    tree = ast.parse(read(path).decode('utf-8'), filename=str(path))
    vals = [n.value for n in tree.body if isinstance(n, ast.Assign)
            and any(isinstance(t, ast.Name) and t.id == name for t in n.targets)]
    assert len(vals) == 1
    return ast.literal_eval(vals[0])


def statement(raw, name):
    hits = re.findall(rb'(?ms)^theorem ' + name.encode() + rb'\s*:\s*(.*?)\s*:= by', raw)
    assert len(hits) == 1
    return hits[0]


def partition(raw):
    incoming, retained = [], []
    for line in raw.splitlines(keepends=True):
        if line.startswith(b'import '):
            hit = re.fullmatch(rb'import ([A-Za-z_][A-Za-z0-9_.]*)\r?\n?', line)
            assert hit
            incoming.append((hit[1].decode('ascii'), line))
        else:
            retained.append(line)
    return incoming, b''.join(retained)


def main():
    m0 = manifest(V0 / 'files.json', '71dce9f3714334dd1f525f037f18ee1c6a4ba25a2b3ac9838df49cc6934879f7')
    m1 = manifest(V1 / 'files.json', 'bde018dbebf0664f5cbc002100d777bd2bcead0a8ce6e2fb75d3d12145999c10')
    outer = manifest(D / 'draft-v1-prepared-files.json', 'cdf8c847e651efbab1a64c2546aa12dc898361acf0edbcfd159c2233e3f96e60')
    repair = manifest(REPAIR / 'files.json', '9aafa909450a60295a0864982d8f3f596217fba54c8e04eeeb3a21eede8f5114')
    flat0, flat1 = read(V0 / 'Solution.lean'), read(V1 / 'Solution.lean')
    assert flat0.count(OLD) == flat1.count(NEW) == 1
    assert flat0.replace(OLD, NEW) == flat1 and flat1.replace(NEW, OLD) == flat0
    assert len(flat1) == 1829955 and len(flat1) - len(flat0) == 20
    assert sha(flat1) == '8928832f3503d39ad6786ae26a394299779d3a53b7c590e7ca7df793ae7614f3'
    changed = [(i + 1, a.decode().rstrip('\n'), b.decode().rstrip('\n'))
               for i, (a, b) in enumerate(zip(flat0.splitlines(keepends=True), flat1.splitlines(keepends=True)))
               if a != b]
    assert len(flat0.splitlines()) == len(flat1.splitlines()) and len(changed) == 1
    core = 'frozen-inputs/StructuralW9A220261020/Core.lean'
    for item in m0['files']:
        path = item['path']
        if path not in ['Solution.lean', 'candidate-parameters.json', core]:
            assert read(V0 / path) == read(V1 / path), path
    full0, full1 = read(V0 / core), read(V1 / core)
    assert full0 == read(ROOT / 'StructuralW9A220261020/Core.lean')
    assert full1 == read(REPAIR / 'canonical-full/StructuralW9A220261020/Core.lean')
    assert full0.replace(OLD, NEW) == full1 and full1.replace(NEW, OLD) == full0
    wrapper = read(V1 / 'frozen-inputs/public-wrapper.lean.txt')
    official = read(V1 / 'frozen-inputs/Challenge.Candidate.lean')
    roots = ['candidate_strict_improvement', 'candidate_critical_line_bound',
             'candidate_critical_line_bound_cumulative']
    statements = []
    for name in roots:
        actual, trusted = statement(flat1, name), statement(official, name)
        assert actual == statement(wrapper, name)
        assert b''.join(actual.split()) == b''.join(trusted.split())
        statements.append({'name': name, 'wrapper_type_sha256': sha(actual),
                           'equals_official_after_whitespace_only': True})
    runner = ROOT / 'research-goal-20261020-w9a2-verification-preparation-v1/run_verification.py'
    header = literal(runner, 'HEADER')
    assert header == literal(D / 'freeze_text.py', 'HEADER')
    incoming, parts, moves, segments = [], [], [], []
    names = ['StructuralW9A220261020.' + name for name in MODULES]
    for name, module in zip(MODULES, names):
        path = 'StructuralW9A220261020/' + name + '.lean'
        raw = read(V1 / 'frozen-inputs' / path)
        imports, body = partition(raw)
        for target, line in imports:
            internal = target in names
            if internal:
                assert names.index(target) < names.index(module)
            else:
                incoming.append(line)
            moves.append({'source': path, 'import': target, 'internal': internal,
                          'removed_line_bytes': len(line), 'removed_line_sha256': sha(line)})
        parts.append((module, body))
    reconstructed = header + b'import ChallengeDeps.CandidateSpec\n' + b''.join(incoming) + b'\n'
    for module, body in parts:
        reconstructed += ('\n/- BEGIN FLATTENED MODULE ' + module + ' -/\n').encode()
        start = len(reconstructed)
        reconstructed += body
        segments.append({'module': module, 'start': start, 'end': len(reconstructed),
                         'retained_non_import_sha256': sha(body)})
        reconstructed += b'\n'
    reconstructed += b'\n' + wrapper
    assert reconstructed == flat1
    params = json.loads(read(V1 / 'candidate-parameters.json'))
    assert params['body_segments'] == segments and params['import_lines_moved'] == moves
    assert params['solution_bytes'] == len(flat1) and params['solution_sha256'] == sha(flat1)
    assert params['source_slack_bytes'] == 2000000 - len(flat1)
    # Catch a changing input rather than silently certifying an earlier snapshot.
    before = dict(INPUTS)
    for path in list(before):
        read(ROOT / path)
    report = {'scope': 'Independent static byte/type-text review only',
        'status': 'PASS_STATIC', 'v0_manifest_rows': len(m0['files']),
        'v1_manifest_rows': len(m1['files']), 'v1_outer_manifest_rows': len(outer['files']),
        'repair_manifest_rows': len(repair['files']), 'input_count': len(before),
        'input_before_after_identical': True, 'inputs': before,
        'flat_bytes': len(flat1), 'flat_sha256': sha(flat1), 'source_limit_bytes': 2000000,
        'source_slack_bytes': 2000000 - len(flat1), 'one_line_delta_bytes': 20,
        'changed_flat_lines': changed, 'forward_and_backward_flat_projection_exact': True,
        'canonical_v0_unchanged': True, 'new_Core_equals_frozen_repair': True,
        'all_v0_companion_trusted_wrapper_bytes_equal': True,
        'reconstruction_from_current_frozen_module_nonimport_bytes_exact': True,
        'import_move_plan_exact': True, 'body_segment_plan_exact': True,
        'three_public_statement_types': statements,
        'proof_compiler_export_kernel_search_runs': 0, 'round_counter_changes': 0,
        'ordinary_comparator_default_kernel_nanoda_or_official_acceptance_proven': False,
        'fresh_record_rechecked': False}
    with (OUT / 'review.json').open('x', encoding='utf-8', newline='\n') as stream:
        json.dump(report, stream, ensure_ascii=False, indent=2)
        stream.write('\n')
    print(json.dumps({k: report[k] for k in ['status', 'input_count', 'flat_bytes', 'flat_sha256',
        'source_slack_bytes', 'changed_flat_lines', 'proof_compiler_export_kernel_search_runs']}, ensure_ascii=False))


if __name__ == '__main__':
    main()
