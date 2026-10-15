"""Extend the verified FinalMult build to every frozen Core import, preserving its receipt."""
import argparse
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import time

REPO = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--setup-dir', type=Path, default=REPO/'tmp/setup-20261015')
args = parser.parse_args()
SETUP = args.setup_dir.resolve()
runtime = json.loads((SETUP/'runtime.json').read_text())
package = Path(runtime['package_root'])/'Zeta23'
compiler = runtime['lean']
env = dict(os.environ, PATH=str(Path(compiler).parent)+':'+os.environ['PATH'], LEAN_PATH=runtime['lean_path'])
logdir = Path(runtime['runtime_root'])/'dependency-logs'
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
prior_path = SETUP/'dependencies-finalmult-135.json'
if not prior_path.exists(): prior_path.write_bytes((SETUP/'dependencies.json').read_bytes())
prior = json.loads(prior_path.read_text())
assert prior['passed'] and prior['cache']['exit_code'] == 0
assert prior['runtime_manifest_sha256'] == sha(SETUP/'runtime.json')
records = {entry['module']:entry for entry in prior['compiled_modules']}
for entry in records.values():
    assert entry['exit_code'] == 0 and entry['source_unchanged']
    assert sha(Path(entry['source'])) == entry['source_sha256']
    assert sha(Path(entry['olean'])) == entry['olean_sha256']
core = REPO/'GramDefect20261015/Core.lean'
core_hash = sha(core)
roots = sorted(set(re.findall(r'^import (Zeta23\.\S+)\s*$', core.read_text(), re.M)) | {'Zeta23.FinalMult'})
order, seen, deps = [], set(), {}
def visit(module):
    if module in seen: return
    seen.add(module)
    source = package/Path(*module.split('.')).with_suffix('.lean')
    imports = re.findall(r'^import (Zeta23\.\S+)\s*$', source.read_text(), re.M)
    deps[module] = imports
    for dep in imports: visit(dep)
    order.append(module)
for module in roots: visit(module)
missing = [module for module in order if module not in records]
print('All Core roots:', ', '.join(roots), flush=True)
print(f'Closure: {len(order)}; validated prior: {len(records)}; missing: {missing}', flush=True)
for module in missing:
    source = package/Path(*module.split('.')).with_suffix('.lean')
    output = package/'.lake/build/lib/lean'/Path(*module.split('.')).with_suffix('.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    command = [compiler,'-j1','--tstack=32768','-DrelaxedAutoImplicit=false','-R',str(package),'-o',str(output),str(source)]
    before, start = sha(source), time.monotonic()
    log = logdir/(module+'.log')
    with log.open('wb') as out:
        process = subprocess.run(command,cwd=package,env=env,stdout=out,stderr=subprocess.STDOUT)
    entry = {'module':module,'command':command,'source':str(source),'source_sha256':before,
        'source_unchanged':before == sha(source),'exit_code':process.returncode,
        'elapsed_seconds':round(time.monotonic()-start,3),'log':str(log),'log_sha256':sha(log),
        'olean':str(output),'olean_sha256':sha(output) if process.returncode == 0 else None}
    (logdir/(module+'.json')).write_text(json.dumps(entry,indent=2)+'\n')
    assert process.returncode == 0 and entry['source_unchanged'], module
    records[module] = entry
    print('Compiled:',module,entry['elapsed_seconds'],flush=True)
assert sha(core) == core_hash
record = {**prior,'compiled_modules':list(records.values()),'root_modules':roots,
    'root_source':str(core),'root_source_sha256':core_hash,'closure_module_count':len(order),
    'previous_dependency_receipt':str(prior_path),'previous_dependency_receipt_sha256':sha(prior_path),
    'extension_compiled_modules':missing,'prior_compilations_reused_by_hash':len(prior['compiled_modules'])}
(SETUP/'dependencies.json').write_text(json.dumps(record,indent=2)+'\n')
(SETUP/'zeta-module-dependencies.json').write_text(json.dumps({module:{'source':str(package/Path(*module.split('.')).with_suffix('.lean')),
    'dependencies':deps[module]} for module in order},indent=2)+'\n')
print('Extended dependencies passed:',len(records),flush=True)
