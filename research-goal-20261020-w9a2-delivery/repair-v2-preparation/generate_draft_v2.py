"""Exclusive text-only draft-v2 from frozen draft-v1 plus sealed Graph proof repair.

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
PRIOR = HERE / 'draft-v1'
REPAIR = ROOT / 'research-goal-20261020-w9a2-graph-repair-v1'
PRIOR_MANIFEST_SHA = 'bde018dbebf0664f5cbc002100d777bd2bcead0a8ce6e2fb75d3d12145999c10'
REPAIR_MANIFEST_SHA = 'a7a9b9090f51919d3f07276a758e333fed135f98a7b854dbe84f755bc4f0de19'
GRAPH = 'StructuralW9A220261020/Graph.lean'
OLD = b'  all_goals norm_num [gsum_range, natGaps, reverse8, Finset.sum_range_succ] <;> ring\r\n'
NEW = b'  all_goals norm_num [gsum_range, natGaps, reverse8, Finset.sum_range_succ] <;> simp only [Fin.reduceFinMk] <;> ring\r\n'
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
    dest = HERE / 'draft-v2'; assert not dest.exists()
    prior_manifest = manifest(PRIOR / 'files.json', PRIOR_MANIFEST_SHA)
    repair_manifest = manifest(REPAIR / 'files.json', REPAIR_MANIFEST_SHA)
    plan = copy.deepcopy(json.loads(read(PRIOR / 'candidate-parameters.json')))
    original = read(PRIOR / 'frozen-inputs' / GRAPH)
    repaired = read(REPAIR / GRAPH)
    assert read(ROOT / GRAPH) == original
    assert original.count(OLD) == repaired.count(NEW) == 1
    assert NEW not in original and OLD not in repaired
    assert original.replace(OLD, NEW) == repaired and repaired.replace(NEW, OLD) == original
    assert len(repaired) == 17366 and len(repaired) - len(original) == 32
    assert sha(repaired) == '9877394187460ee686e31561fe8f1ccb5015eb29fa2b7f5c2565071351add00c'
    oldlines, newlines = original.splitlines(keepends=True), repaired.splitlines(keepends=True)
    assert len(oldlines) == len(newlines)
    assert [(i+1, a, b) for i, (a, b) in enumerate(zip(oldlines, newlines)) if a != b] == [(151, OLD, NEW)]
    marker = b'theorem reverse_span '
    def theorem(raw):
        assert raw.count(marker) == 1
        a = raw.index(marker); b = raw.index(b':= by', a)
        return raw[a:b]
    assert theorem(original) == theorem(repaired)
    sdk = ROOT / 'tmp/lean-toolchain/src/lean/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Fin.lean'
    sdkraw = read(sdk)
    assert sha(sdkraw) == '6e22f4a410ec146af6481c30693c141c4f9d120db24e5d2bc5a1e6a873915bdc'
    assert b'builtin_dsimproc [simp, seval] reduceFinMk (Fin.mk _ _)' in sdkraw
    header = literal(HERE / 'freeze_text.py', 'HEADER')
    runner = ROOT / 'research-goal-20261020-w9a2-verification-preparation-v1/run_verification.py'
    assert sha(read(runner)) == '92cc8dcf3e3c46e76490ba7bfe8d93bc10e331131eaab3b4c3ae500f80ac66a8'
    assert literal(runner, 'HEADER') == header
    names = [entry['module'] for entry in plan['source_modules']]
    imports, parts, sources, origins = [], [], [], []
    for entry in plan['source_modules']:
        path, module = entry['path'], entry['module']
        source = REPAIR / path if path == GRAPH else PRIOR / 'frozen-inputs' / path
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
    assert len(result) == 1829987 and len(result) <= 2000000
    types = []
    official = read(PRIOR / 'frozen-inputs/Challenge.Candidate.lean')
    for name in plan['public_roots']:
        pattern = rb'(?ms)^theorem ' + name.encode() + rb'\s*:\s*(.*?)\s*:= by'
        actual, expected = re.findall(pattern, wrapper), re.findall(pattern, official)
        assert len(actual) == len(expected) == 1 and b''.join(actual[0].split()) == b''.join(expected[0].split())
        types.append({'name': name, 'type_sha256': sha(actual[0]), 'unchanged_and_official_mod_whitespace': True})
    plan.update(solution_bytes=len(result), solution_sha256=sha(result), source_slack_bytes=2000000-len(result),
        source_modules=sources, body_segments=segments, source_revision='draft-v2-one-existing-Fin-simproc-in-Graph-proof',
        repair_manifest_sha256=REPAIR_MANIFEST_SHA, previous_draft_manifest_sha256=PRIOR_MANIFEST_SHA)
    review = {'scope': 'Independent byte-only delivery review; no semantic/proof execution',
        'repair_manifest_rows_verified': len(repair_manifest['files']),
        'previous_draft_manifest_rows_verified': len(prior_manifest['files']),
        'theorem': 'StructuralW9A220261020.Graph.reverse_span', 'theorem_statement_sha256': sha(theorem(original)),
        'same_theorem_statement': True, 'changed_Graph_line': 151, 'byte_delta': 32,
        'old_line': OLD.decode().rstrip('\r\n'), 'new_line': NEW.decode().rstrip('\r\n'),
        'Graph_forward_and_reverse_projection_exact': True,
        'all_bytes_outside_single_proof_line_unchanged': True,
        'all_definitions_data_134_edges_2267_exclusions_StateAt_cost_threshold_bytes_unchanged': True,
        'four_other_modules_and_whole_wrapper_from_frozen_draft_v1_byte_identical': True,
        'single_file_forward_and_reverse_projection_exact': True, 'public_statement_types': types,
        'trusted_inputs_byte_identical_to_frozen_draft_v1': True,
        'canonical_Graph_v0_unchanged': True, 'all_previous_drafts_and_manifests_preserved': True,
        'proof_compiler_export_kernel_search_runs': 0, 'ordinary_Graph_pass_claimed': False,
        'Comparator_passed': False, 'independent_kernels_passed': False, 'complete_3200s_passed': False,
        'official_accepted': False, 'main_round_counter_changed': False}
    dest.mkdir()
    for folder in ['frozen-inputs', 'trusted']:
        for source in sorted((PRIOR / folder).rglob('*')):
            if source.is_file():
                relative = source.relative_to(PRIOR).as_posix()
                write(dest / relative, repaired if relative == 'frozen-inputs/' + GRAPH else read(source))
    write(dest / 'Solution.lean', result)
    write(dest / 'candidate-parameters.json', dump(plan))
    write(dest / 'source-review.json', dump(review))
    write(dest / 'source-origins.json', dump({'scope': 'Text source bindings only', 'module_inputs': origins,
        'previous_draft_manifest': row(PRIOR / 'files.json', ROOT),
        'Graph_repair_manifest': row(REPAIR / 'files.json', ROOT), 'sdk_Fin_source': row(sdk, ROOT),
        'wrapper': row(PRIOR / 'frozen-inputs/public-wrapper.lean.txt', ROOT)}))
    diff = ''.join(difflib.unified_diff(prior.decode().splitlines(keepends=True),
        result.decode().splitlines(keepends=True), fromfile='draft-v1/Solution.lean', tofile='draft-v2/Solution.lean'))
    write(dest / 'Solution-v1-to-v2.diff', diff.encode())
    manifest(PRIOR / 'files.json', PRIOR_MANIFEST_SHA)
    manifest(REPAIR / 'files.json', REPAIR_MANIFEST_SHA)
    assert read(ROOT / GRAPH) == original
    files = [row(p, dest) for p in sorted(dest.rglob('*')) if p.is_file()]
    write(dest / 'files.json', dump({'scope': 'Unverified source preparation only', 'files': files}))
    print(json.dumps({'version': 'draft-v2', 'solution_bytes': len(result), 'solution_sha256': sha(result),
        'manifest_sha256': sha(read(dest / 'files.json')), 'source_slack_bytes': 2000000-len(result),
        'upload_ready': False, 'proof_compiler_export_kernel_search_runs': 0}))


if __name__ == '__main__':
    main()
