"""Prepare a non-executable candidate ordinary gate proposal; no subprocess."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
RUNTIME = ROOT / 'research-goal-20261020-w9a2-runtime'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def relative(path):
    return path.relative_to(ROOT).as_posix()


def main():
    setup = json.loads((RUNTIME / 'trusted-setup-gate-v1.json').read_text(encoding='utf-8'))
    split_root = HERE / 'development-split'
    targets = []
    paths = []
    for name in ['Prefix', 'Core', 'Graph', 'Localization', 'Counting', 'Final']:
        source_root = split_root if name in ['Prefix', 'Core'] else ROOT
        source = source_root / f'StructuralW9A220261020/{name}.lean'
        module = f'StructuralW9A220261020.{name}'
        assert source.relative_to(source_root).with_suffix('').as_posix().replace('/', '.') == module
        printed = re.findall(r'^#print axioms ([^\s]+)', source.read_text(encoding='utf-8'), re.M)
        targets.append({'module': module, 'source': relative(source),
                        'source_root': relative(source_root) if source_root != ROOT else '.',
                        'printed_roots': printed})
        paths.append(source)
    assert len(targets[-2]['printed_roots']) == 5
    assert len(targets[-1]['printed_roots']) == 7
    assert all(not row['printed_roots'] for row in targets[:4])
    runner = RUNTIME / 'compile_frozen.py'
    paths += [runner, RUNTIME / 'trusted/ChallengeDeps.lean',
              ROOT / 'StructuralW9A220261020/Core.lean',
              ROOT / 'research-goal-20261019-w9a2-record/official/proof/Solution.lean',
              ROOT / 'research-goal-20261019-w9a2-certificate-analysis/geometry-audit.json',
              ROOT / 'research-goal-20261019-w9a2-certificate-analysis/numeric-leaves-sorted.jsonl.gz',
              HERE / 'files.json', HERE / 'split-files.json']
    assert len(paths) == len(set(paths))
    pins = [{'path': relative(p), 'sha256': sha(p)} for p in paths]
    assert all(row['source'] in {p['path'] for p in pins} for row in targets)
    known_modules = set()
    for row in targets:
        text = (ROOT / row['source']).read_text(encoding='utf-8')
        imports = re.findall(r'^import (StructuralW9A220261020\.[^\s]+)', text, re.M)
        assert set(imports) <= known_modules, (row['module'], imports, known_modules)
        known_modules.add(row['module'])
    proposal = {
        'authorized': False,
        'proposal_only': True,
        'task': 'w9a2-ordinary-source-pinned',
        'scope': 'One candidate-only ordinary development batch after a separate trusted-dependency setup. No exporter, Comparator, nanoda, solver, source repair, or production acceptance.',
        'automatic_repairs_or_retries': 0,
        'sole_candidate_compiler_owner': '/root/formal_owner',
        'runner_sha256': sha(runner),
        'lean': setup['lean'],
        'source_files': pins,
        'packages': setup['packages'],
        'package_libs': setup['package_libs'],
        'work_directory': 'tmp/w9a2-20261020/candidate-ordinary-v0',
        'reused_oleans': [{'path': 'tmp/w9a2-20261020/trusted-v1/lib/ChallengeDeps.olean',
                           'module_path': 'ChallengeDeps.olean',
                           'sha256': None}],
        'targets': targets,
        'pending_before_root_freeze': [
            'Select Windows setup v1 or a separately prepared Linux runner/environment; current runner is Windows-specific.',
            'Inspect actual trusted setup terminal/receipt exit0 and source identity; fill exact ChallengeDeps.olean hash and final trusted path.',
            'Recheck all source and runner hashes, selected toolchain identity and package commits, fresh no-other-Lean condition.',
            'Root creates a new explicitly authorized gate and pins its exact hash; this proposal is not executable authorization.'
        ],
        'static_source_root_check_passed': True,
        'static_dependency_order_check_passed': True,
        'static_each_target_source_is_pinned': True,
        'known_limits': [
            'Package source commits are pinned; runner does not hash every compiled dependency olean.',
            'Source files are pre/post hashed but compiled by original path; concurrent source mutation must remain prohibited.',
            'Prefix/Core split is for development only; no single-file or cold production-budget claim.',
            'No candidate olean is reused; only the separately built trusted definition module is proposed for reuse.'
        ],
        'candidate_compiler_runs': 0,
    }
    with (HERE / 'candidate-ordinary-gate-proposal.json').open('x', encoding='utf-8', newline='\n') as stream:
        json.dump(proposal, stream, ensure_ascii=False, indent=2)
        stream.write('\n')
    print(json.dumps({'authorized': False, 'targets': len(targets),
                      'pinned_files': len(pins), 'hash': sha(HERE / 'candidate-ordinary-gate-proposal.json')}))


if __name__ == '__main__':
    main()
