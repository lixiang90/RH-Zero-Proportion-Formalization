"""P preparation only: AST, immutable bytes, saved scalar metadata, runtime."""
from pathlib import Path
from hashlib import sha256
import ast
import json
import os
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

def pin(path):
    h = sha256()
    with path.open('rb') as handle:
        for block in iter(lambda: handle.read(1048576), b''): h.update(block)
    return h.hexdigest()
def row(path): return {'path': path.relative_to(ROOT).as_posix(), 'bytes': path.stat().st_size, 'sha256': pin(path)}
def load(path): return json.loads(path.read_text(encoding='utf-8'))
def write(path, value):
    with path.open('x', encoding='utf-8', newline='\n') as handle:
        json.dump(value, handle, indent=2); handle.write('\n'); handle.flush(); os.fsync(handle.fileno())
def literal(tree, name):
    nodes = [node for node in tree.body if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == name for t in node.targets)]
    assert len(nodes) == 1; return ast.literal_eval(nodes[0].value)

def main():
    for name in ['preparation.json', 'prepared-files.json', 'started.json', 'launch.json', 'result.json', 'failure.json',
                 'recovery.json', 'progress-commits.jsonl', 'case-records.jsonl.gz']:
        assert not (HERE / name).exists(), ('prepare_before_any_execution', name)
    names = ['continue_once.py', 'recover_frozen.py', 'fixed_curvature.py', 'deduction_transfer.py',
             'run_once.py', 'selector_inventory.py', 'prepare_freeze.py']
    trees = {name: ast.parse((HERE / name).read_text(encoding='utf-8'), filename=str(HERE / name)) for name in names}
    assert 'os.replace(' not in (HERE / 'continue_once.py').read_text(encoding='utf-8')
    deps = {}
    def add(name, expected=None, size=None):
        path = (ROOT / name).resolve(); assert path.is_relative_to(ROOT); actual = row(path)
        if expected is not None: assert actual['sha256'] == expected, (name, actual['sha256'], expected)
        if size is not None: assert actual['bytes'] == size
        if name in deps: assert deps[name] == actual
        deps[name] = actual
    for name, expected in literal(trees['continue_once.py'], 'PINS').items():
        add(name, expected)
        for field in ['files', 'owned_files', 'read_only_dependencies', 'read_only_existing_references',
                      'dependencies', 'read_only_whole_file_dependencies']:
            for item in load(ROOT / name).get(field, []): add(item['path'], item['sha256'], item.get('bytes'))
    n2 = load(ROOT / 'research-goal-20261018-stageN2-pooled-component-resumption/result.json')
    assert n2['committed_records'] == 2375 and n2['total_LP_calls'] == 2374
    assert n2['counts'] == {'Lower': 2373, 'deduction_Lower': 1, 'Below': 1}
    assert n2['repeated_old_LP_calls'] == 0
    O = load(ROOT / 'research-goal-20261018-stageO-fixed-curvature-preparation/result.json')
    assert O['conditional_fixed_pair_floor_closes'] and O['original_REG_cell_queries'] == 23
    runtime = load(ROOT / 'research-goal-20261018-stageM-component-envelope-preparation/external-runtime.json')
    for item in runtime['files']:
        path = Path(item['path']); assert pin(path) == item['sha256'] and path.stat().st_size == item['bytes']
    assert str(Path(sys.executable)) == runtime['python_executable']
    cli = [runtime['python_executable'], '-B', '-X', 'utf8',
           'research-goal-20261018-stageP-complete-curvature-preparation/run_once.py',
           '--launch-authorized-complete-curvature-P', '--gate', '<ROOT_GATE_PATH>', '--gate-sha256', '<ROOT_GATE_SHA256>']
    receipt = {'schema': 'P-complete-fixed-curvature-AST-and-byte-preparation-v1', 'passed': True,
        'source_files': [{**row(HERE / name), 'AST_parse_passed': True} for name in names],
        'read_only_dependencies': [deps[name] for name in sorted(deps)], 'external_runtime_files': runtime['files'],
        'saved_scalar_metadata': {'original_H_range': 15378, 'recover_records': 2375, 'previous_calls': 2374,
            'remaining_records': 13003, 'maximum_new_calls': 13002, 'O_seed_cells': 23, 'original_REG_catalog': 266},
        'command_template': cli, 'producer_modules_imported': 0, 'mathematical_gzip_members_decoded': 0,
        'FS_curvature_matrix_LP_Laplace_newpoint_kernel_or_Lean_executions': 0,
        'actual_bridge_and_execution_gate_pending': True, 'generic_source_runtime_payload_budget': 'unknown'}
    write(HERE / 'preparation.json', receipt)
    owned = names + ['SPEC.zh.md', 'required-gate-fields.json', 'preparation.json']
    manifest = {'schema': 'P-complete-pooled-fixed-curvature-prepared-only-v1', 'files': [row(HERE / name) for name in owned],
        'read_only_dependencies': [deps[name] for name in sorted(deps)], 'external_read_only_runtime_files': runtime['files'],
        'mathematical_executions': 0, 'solver_calls': 0, 'immutable_root_execution_gate_required': True,
        'stop_policy': 'first_nonclosed_case_after_at_most_one_fixed_curvature_attempt',
        'source_runtime_and_unconditional_record_proven': False, 'mutable_governance_not_a_dependency': True}
    write(HERE / 'prepared-files.json', manifest)
    print(json.dumps({'prepared_only': True, 'manifest': row(HERE / 'prepared-files.json'),
        'sources': {name: pin(HERE / name) for name in names}, 'read_dependencies': len(deps),
        'mathematical_executions': 0, 'solver_calls': 0}))

if __name__ == '__main__': main()
