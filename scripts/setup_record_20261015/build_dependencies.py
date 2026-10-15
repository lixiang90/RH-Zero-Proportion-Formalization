"""Freshly build the pinned Zeta23 closure of every frozen Core import."""
import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import time

REPOSITORY = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--setup-dir', type=Path, default=REPOSITORY / 'tmp/setup-20261015')
parser.add_argument('--root-source', type=Path, default=REPOSITORY / 'GramDefect20261015/Core.lean')
args = parser.parse_args()
ARCHIVES = args.setup_dir.resolve()
RUNTIME = json.loads((ARCHIVES / 'runtime.json').read_text())
ROOT = Path(RUNTIME['runtime_root'])
PACKAGES = Path(RUNTIME['package_root'])
LEAN = RUNTIME['lean']
ENV = dict(os.environ, PATH=str(Path(LEAN).parent) + ':' + os.environ['PATH'],
           LEAN_PATH=RUNTIME['lean_path'], MATHLIB_CACHE_DIR=RUNTIME['cache'],
           LEAN_SRC_PATH=':'.join(str(p) for p in PACKAGES.iterdir() if p.is_dir()))
LOGS = ROOT / 'dependency-logs'
LOGS.mkdir(exist_ok=True)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def strip_comments(text):
    out, pos, depth = [], 0, 0
    while pos < len(text):
        if text.startswith('/-', pos):
            depth += 1; pos += 2
        elif depth and text.startswith('-/', pos):
            depth -= 1; pos += 2
        elif depth:
            if text[pos] == '\n': out.append('\n')
            pos += 1
        elif text.startswith('--', pos):
            end = text.find('\n', pos)
            pos = len(text) if end < 0 else end
        else:
            out.append(text[pos]); pos += 1
    return ''.join(out)

modules, mathlib, seen = {}, set(), set()
def visit(module):
    if module in seen: return
    seen.add(module)
    if module.startswith('Zeta23.'):
        source = PACKAGES / 'Zeta23' / Path(*module.split('.')).with_suffix('.lean')
        imports = []
        for line in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)', strip_comments(source.read_text()), re.M):
            imports.extend(line.split())
        modules[module] = {'source': source, 'dependencies': [m for m in imports if m.startswith('Zeta23.')]}
        for dep in imports: visit(dep)
    elif module.startswith('Mathlib.') or module == 'Mathlib':
        mathlib.add(module)
root_source = args.root_source.resolve()
root_source_sha256 = digest(root_source)
root_imports = []
for line in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)', strip_comments(root_source.read_text()), re.M):
    root_imports.extend(line.split())
root_modules = sorted(set([module for module in root_imports if module.startswith('Zeta23.')] + ['Zeta23.FinalMult']))
for module in root_imports + ['Zeta23.FinalMult']:
    visit(module)
print(f'Closure: {len(modules)} Zeta23 modules, {len(mathlib)} direct Mathlib roots', flush=True)
(ARCHIVES / 'zeta-module-dependencies.json').write_text(json.dumps({m: {'source': str(v['source']),
    'dependencies': v['dependencies']} for m,v in modules.items()}, indent=2) + '\n')
cache_modules = ['Cache.Lean', 'Batteries.Tactic.OpenPrivate', 'Cache.IO', 'Cache.Cli', 'Cache.Infra',
                 'Cache.Hashing', 'Cache.Requests', 'Cache.Marker', 'Cache.Query', 'Cache.Warning']
for module in cache_modules:
    package = 'batteries' if module.startswith('Batteries.') else 'mathlib'
    source = PACKAGES / package / Path(*module.split('.')).with_suffix('.lean')
    output = PACKAGES / package / '.lake/build/lib/lean' / Path(*module.split('.')).with_suffix('.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    log = LOGS / ('bootstrap-' + module + '.log')
    with log.open('wb') as out:
        process = subprocess.run([LEAN, '-R', str(PACKAGES / package), '-o', str(output), str(source)],
                                 env=ENV, cwd=PACKAGES / package, stdout=out, stderr=subprocess.STDOUT)
    assert process.returncode == 0, 'Cache bootstrap failed: ' + str(log)
cache_command = [LEAN, '--run', str(PACKAGES / 'mathlib/Cache/Main.lean'), 'get', *sorted(mathlib)]
started = time.monotonic()
with (LOGS / 'mathlib-cache.log').open('wb') as out:
    result = subprocess.run(cache_command, env=ENV, cwd=PACKAGES / 'mathlib', stdout=out, stderr=subprocess.STDOUT)
cache_record = {'command': cache_command, 'exit_code': result.returncode, 'elapsed_seconds': time.monotonic()-started,
                'log': str(LOGS / 'mathlib-cache.log'), 'log_sha256': digest(LOGS / 'mathlib-cache.log')}
(ARCHIVES / 'mathlib-cache.json').write_text(json.dumps(cache_record, indent=2) + '\n')
assert result.returncode == 0, 'Mathlib cache failed: ' + str(LOGS / 'mathlib-cache.log')
print('Mathlib cache ready', flush=True)

def compile_module(module):
    source = modules[module]['source']
    output = PACKAGES / 'Zeta23/.lake/build/lib/lean' / Path(*module.split('.')).with_suffix('.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    log = LOGS / (module + '.log')
    command = [LEAN, '-j1', '--tstack=32768', '-DrelaxedAutoImplicit=false',
               '-R', str(PACKAGES / 'Zeta23'), '-o', str(output), str(source)]
    before = digest(source)
    start = time.monotonic()
    with log.open('wb') as out:
        process = subprocess.run(command, cwd=PACKAGES / 'Zeta23', env=ENV, stdout=out, stderr=subprocess.STDOUT)
    receipt = {'module': module, 'command': command, 'source': str(source), 'source_sha256': before,
        'source_unchanged': before == digest(source), 'exit_code': process.returncode,
        'elapsed_seconds': round(time.monotonic()-start,3), 'log': str(log), 'log_sha256': digest(log),
        'olean': str(output), 'olean_sha256': digest(output) if process.returncode == 0 else None}
    (LOGS / (module + '.json')).write_text(json.dumps(receipt, indent=2) + '\n')
    assert process.returncode == 0 and receipt['source_unchanged'], 'Failed module: ' + module
    return receipt

done, active, receipts, remaining = set(), {}, [], set(modules)
with ThreadPoolExecutor(max_workers=4) as pool:
    while remaining or active:
        for module in sorted(remaining):
            if len(active) >= 4: break
            if set(modules[module]['dependencies']) <= done:
                active[pool.submit(compile_module, module)] = module
                remaining.remove(module)
        if not active: raise RuntimeError('Unresolved dependency graph')
        finished, _ = wait(active, return_when=FIRST_COMPLETED)
        for future in finished:
            module = active.pop(future)
            receipts.append(future.result())
            done.add(module)
            print(f'{len(done)}/{len(modules)} {module}', flush=True)
        (ARCHIVES / 'dependency-build-progress.json').write_text(json.dumps({'completed': len(done),
            'total': len(modules), 'active': list(active.values()), 'completed_modules': receipts}, indent=2)+'\n')
record = {'passed': True, 'cache': cache_record, 'compiled_modules': receipts,
          'runtime_manifest_sha256': digest(ARCHIVES / 'runtime.json'),
          'root_modules': root_modules, 'root_source': str(root_source),
          'root_source_sha256': root_source_sha256, 'closure_module_count': len(modules)}
assert digest(root_source) == root_source_sha256, 'Frozen Core source changed during dependency build'
(ARCHIVES / 'dependencies.json').write_text(json.dumps(record, indent=2) + '\n')
print('Pinned dependency build complete', flush=True)
