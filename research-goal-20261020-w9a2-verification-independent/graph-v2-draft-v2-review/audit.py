"""Static independent Graph repair v2 and frozen draft-v2 byte review."""
import ast
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent
G1 = ROOT / 'research-goal-20261020-w9a2-graph-repair-v1'
G2 = ROOT / 'research-goal-20261020-w9a2-graph-repair-v2'
D = ROOT / 'research-goal-20261020-w9a2-delivery'
V1, V2 = D / 'draft-v1', D / 'draft-v2'
P = 'StructuralW9A220261020/Graph.lean'
A = b'  all_goals norm_num [gsum_range, natGaps, reverse8, Finset.sum_range_succ] <;> ring\r\n'
B = A.replace(b' <;> ring', b' <;> simp only [Fin.reduceFinMk] <;> ring')
C = B.replace(b'<;> simp only [Fin.reduceFinMk]', b'<;> (try simp only [Fin.reduceFinMk])')
SEEN = {}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read(path):
    raw = path.read_bytes()
    key = path.resolve().relative_to(ROOT.resolve()).as_posix()
    val = {'bytes': len(raw), 'sha256': sha(raw)}
    assert SEEN.setdefault(key, val) == val, key
    return raw


def manifest(path, expected):
    raw = read(path)
    assert sha(raw) == expected
    value = json.loads(raw)
    assert len(value['files']) == len({item['path'] for item in value['files']})
    for item in value['files']:
        target = (path.parent / item['path']).resolve()
        assert target.is_relative_to(path.parent.resolve())
        actual = read(target)
        assert len(actual) == item['bytes'] and sha(actual) == item['sha256']
    return value


def statement(raw, name):
    found = re.findall(rb'(?ms)^theorem ' + name.encode() + rb'\s*:\s*(.*?)\s*:= by', raw)
    assert len(found) == 1
    return found[0]


def main():
    m1 = manifest(G1 / 'files.json', 'a7a9b9090f51919d3f07276a758e333fed135f98a7b854dbe84f755bc4f0de19')
    m2 = manifest(G2 / 'files.json', '5e5162d27f6e99347c425b954135db00f4e729b53ba4a430c2b26b4a8eb186a9')
    d1 = manifest(V1 / 'files.json', 'bde018dbebf0664f5cbc002100d777bd2bcead0a8ce6e2fb75d3d12145999c10')
    d2 = manifest(V2 / 'files.json', '4bdee1454b87659360f845d9e62c6d842002a10edfa359d24c28f80a714f5f20')
    outer = manifest(D / 'draft-v2-prepared-files.json', '299ae8f81358a8d1c27e41a1360752abbc63a8ced19c42ea72ce92518a6edab1')
    graph0, graph1, graph2 = read(ROOT / P), read(G1 / P), read(G2 / P)
    assert graph0 == read(G1 / 'Graph-v0.lean')
    assert graph0.count(A) == graph1.count(B) == graph2.count(C) == 1
    assert graph0.replace(A, B) == graph1 and graph1.replace(B, A) == graph0
    assert graph1.replace(B, C) == graph2 and graph2.replace(C, B) == graph1
    assert graph0.replace(A, C) == graph2 and graph2.replace(C, A) == graph0
    assert len(graph2)-len(graph1) == 6 and len(graph2)-len(graph0) == 38
    assert len(graph2) == 17372 and sha(graph2) == '2e259252f7fa993954bd52c4a6d6ec58594116a500a576910d6fa671d6521966'
    differences = [i+1 for i, (a,b) in enumerate(zip(graph1.splitlines(), graph2.splitlines())) if a != b]
    assert differences == [151] and graph2.count(b'\r\n') == graph1.count(b'\r\n') == 222
    graph_st = [re.findall(rb'(?ms)^theorem reverse_span (.*?) := by\r?\n', g) for g in [graph0,graph1,graph2]]
    assert len(graph_st[0]) == 1 and graph_st[0] == graph_st[1] == graph_st[2]
    job = ROOT / 'tmp/w9a2-20261020/candidate-ordinary-v2'
    for item in m2['files']:
        if item['path'].startswith('failed-v1-evidence/'):
            assert read(G2 / item['path']) == read(job / Path(item['path']).name)
    log = read(G2 / 'failed-v1-evidence/StructuralW9A220261020_Graph.log')
    receipt = json.loads(read(G2 / 'failed-v1-evidence/StructuralW9A220261020_Graph.receipt.json'))
    terminal = json.loads(read(G2 / 'failed-v1-evidence/terminal.json'))
    note = json.loads(read(G2 / 'repair.json'))
    assert log.count(b'error:') == 1 and b'`simp` made no progress' in log
    assert receipt['exit_code'] == 1 and receipt['source_sha256'] == sha(graph1) and receipt['log_sha256'] == sha(log)
    assert terminal['passed'] is False and note['root_observed_previous_parent_session'] == 42867
    assert note['actual_parent_exit_code'] == 1
    flat1, flat2 = read(V1 / 'Solution.lean'), read(V2 / 'Solution.lean')
    assert flat1.count(A) == flat2.count(B) == 1
    assert flat1.replace(A, B) == flat2 and flat2.replace(B, A) == flat1
    assert len(flat2) == 1829987 and sha(flat2) == '43cfdfddf4282e29c5f7f251ce6b33462964919173104efe0533438097c5107b'
    for item in d1['files']:
        path = item['path']
        if path.startswith(('frozen-inputs/', 'trusted/')) and path != 'frozen-inputs/' + P:
            assert read(V1 / path) == read(V2 / path), path
    assert read(V2 / 'frozen-inputs' / P) == graph1
    wrapper = read(V2 / 'frozen-inputs/public-wrapper.lean.txt')
    official = read(V2 / 'frozen-inputs/Challenge.Candidate.lean')
    roots = ['candidate_strict_improvement', 'candidate_critical_line_bound', 'candidate_critical_line_bound_cumulative']
    types = []
    for name in roots:
        val = statement(flat2, name)
        assert val == statement(flat1, name) == statement(wrapper, name)
        assert b''.join(val.split()) == b''.join(statement(official, name).split())
        types.append({'name': name, 'type_sha256': sha(val)})
    tree = ast.parse(read(ROOT / 'research-goal-20261020-w9a2-verification-preparation-v1/run_verification.py').decode())
    header = [ast.literal_eval(n.value) for n in tree.body if isinstance(n, ast.Assign)
              and any(isinstance(t, ast.Name) and t.id == 'HEADER' for t in n.targets)]
    assert len(header) == 1
    names = ['StructuralW9A220261020.' + n for n in ['Core','Graph','Localization','Counting','Final']]
    external, parts = [], []
    for module in names:
        raw = read(V2 / 'frozen-inputs' / (module.replace('.', '/') + '.lean'))
        body = []
        for line in raw.splitlines(keepends=True):
            if line.startswith(b'import '):
                target = line[len(b'import '):].strip().decode()
                if target not in names: external.append(line)
            else: body.append(line)
        parts.append((module, b''.join(body)))
    rebuilt = header[0] + b'import ChallengeDeps.CandidateSpec\n' + b''.join(external) + b'\n'
    for name, body in parts:
        rebuilt += ('\n/- BEGIN FLATTENED MODULE ' + name + ' -/\n').encode() + body + b'\n'
    rebuilt += b'\n' + wrapper
    assert rebuilt == flat2
    before = dict(SEEN)
    for name in list(before): read(ROOT / name)
    result = {'scope': 'Independent static Graph repair v2 and draft-v2 review only',
        'status': 'PASS_STATIC', 'manifest_rows': {'Graph_v1': len(m1['files']), 'Graph_v2': len(m2['files']),
            'draft_v1': len(d1['files']), 'draft_v2': len(d2['files']), 'draft_v2_outer': len(outer['files'])},
        'input_count': len(before), 'input_before_after_identical': True, 'inputs': before,
        'graph_v1_to_v2_single_line': 151, 'graph_v1_to_v2_delta_bytes': 6,
        'graph_v0_to_v2_delta_bytes': 38, 'graph_v2_bytes': len(graph2), 'graph_v2_sha256': sha(graph2),
        'all_forward_backward_projections_exact': True, 'canonical_Graph_v0_unchanged': True,
        'same_reverse_span_type_sha256': sha(graph_st[0][0]), 'all_other_definition_data_api_bytes_unchanged': True,
        'try_scope': 'At each residual norm_num goal, try the existing explicit Fin simp; the original ring always follows every surviving goal.',
        'failure_evidence_exact_copy': True, 'previous_parent_session_from_root_attestation': 42867,
        'previous_actual_parent_exit_from_root_attestation': 1,
        'sole_log_error': '`simp` made no progress', 'previous_module_receipt_exit_code': 1,
        'draft_v2_bytes': len(flat2), 'draft_v2_sha256': sha(flat2), 'draft_v2_delta_bytes': 32,
        'draft_v2_independent_full_byte_reconstruction_exact': True,
        'draft_v2_frozen_other_four_modules_wrapper_trusted_identical_to_v1': True,
        'three_public_types': types, 'compiler_export_kernel_search_runs': 0, 'round_counter_changes': 0,
        'Graph_v2_ordinary_pass_claimed': False, 'whole_submission_verified': False}
    with (OUT/'review.json').open('x',encoding='utf-8',newline='\n') as stream:
        json.dump(result,stream,ensure_ascii=False,indent=2); stream.write('\n')
    print(json.dumps({k: result[k] for k in ['status','input_count','graph_v2_sha256','graph_v1_to_v2_delta_bytes','draft_v2_sha256','compiler_export_kernel_search_runs']}))


if __name__ == '__main__': main()
