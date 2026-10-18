"""Byte identities and AST only. This program does not import the runner or Lean."""
import ast
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent


def item(path):
    data = path.read_bytes()
    return {'path': path.relative_to(ROOT).as_posix(), 'bytes': len(data),
            'sha256': hashlib.sha256(data).hexdigest()}


def main():
    owned = ['compile_phaseA.py', 'required-compiler-gate.json',
             'compiler-runtime-observation.json', 'prepare_compiler.py']
    for name in ['compile_phaseA.py', 'prepare_compiler.py']:
        ast.parse((HERE / name).read_text(encoding='utf-8'), filename=name)
    deps = [HERE / 'phaseA-prepared.json', ROOT / 'tmp/setup-20261015/runtime.json']
    py = Path(sys.executable)
    result = {
        'schema': 'M-actual-Lean-phaseA-compiler-prepared-v1',
        'files': [item(HERE / name) for name in owned],
        'dependencies': [item(path) for path in deps],
        'initial_source_manifest': 'research-goal-20261018-stageM-lean-implementation/phaseA-prepared.json',
        'initial_sources_are_checked_at_execution': True,
        'AST_parsed_without_import': True,
        'Python_executable': {'path': str(py), 'bytes': py.stat().st_size,
            'sha256': hashlib.sha256(py.read_bytes()).hexdigest()},
        'Lean_runs': 0, 'separate_immutable_gate_required': True,
        'command_template': [str(py),
            'research-goal-20261018-stageM-lean-implementation/compile_phaseA.py',
            '--gate', 'ROOT_SUPPLIED_GATE_PATH', '--gate-sha256', 'ROOT_SUPPLIED_GATE_SHA256'],
        'flags': ['-j1', '-M13500', '--tstack=262144',
            '-DrelaxedAutoImplicit=false', '-DElab.async=false'],
        'scope': ['CurrentPrefix', 'QuantizedComponent', 'Sparse78'],
        'repair_policy': 'At most three separate syntax/API/tactic repair versions of the same mathematical theorems; no automatic repair/retry.',
        'outputs': 'tmp/current-s1r-M-20261018/lib; versioned immutable snapshots/logs/resources/receipts',
    }
    out = HERE / 'compiler-prepared.json'
    with out.open('x', encoding='utf-8', newline='\n') as f:
        json.dump(result, f, ensure_ascii=False, indent=2)
        f.write('\n')
    print(json.dumps(item(out)))


if __name__ == '__main__':
    main()
