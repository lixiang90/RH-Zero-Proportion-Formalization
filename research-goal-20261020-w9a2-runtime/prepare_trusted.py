"""Freeze trusted-definition setup; no proof compiler is invoked here."""
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


trusted = HERE / 'trusted'
trusted.mkdir(exist_ok=True)
source = ROOT / 'verification/gram-defect-single-20261014/trusted/ChallengeDeps.lean'
assert sha(source) == 'f05666d0745edbf2dac6ce2a4de675abd1bba3c336fe24aebb80f27d1365ebbd'
dest = trusted / 'ChallengeDeps.lean'
if dest.exists():
    assert sha(dest) == sha(source)
else:
    dest.write_bytes(source.read_bytes())
lean = Path('C:/Users/A/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lean.exe')
names = ['LeanSearchClient','Qq','plausible','Cli','importGraph','proofwidgets',
         'aesop','batteries','Zeta23','mathlib']
packages = []
libs = []
for name in names:
    path = ROOT / '.lake/packages' / name
    revision = subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
    packages.append({'path':path.relative_to(ROOT).as_posix(),'commit':revision})
    lib = path / '.lake/build/lib/lean'
    if lib.is_dir():
        libs.append(lib.relative_to(ROOT).as_posix())
gate = {'authorized':True, 'task':'w9a2-ordinary-source-pinned',
        'scope':'Trusted ChallengeDeps definitions only; relocated Windows package setup. No candidate proof or final kernel claim.',
        'automatic_repairs_or_retries':0,
        'runner_sha256':sha(HERE/'compile_frozen.py'),
        'lean':{'path':str(lean),'sha256':sha(lean),
                'version':subprocess.check_output([lean,'--version'],text=True).strip()},
        'source_files':[{'path':p.relative_to(ROOT).as_posix(),'sha256':sha(p)} for p in
                        [HERE/'compile_frozen.py',trusted/'ChallengeDeps.lean']],
        'packages':packages,'package_libs':libs,
        'work_directory':'tmp/w9a2-20261020/trusted-v0',
        'targets':[{'module':'ChallengeDeps',
                    'source':(trusted/'ChallengeDeps.lean').relative_to(ROOT).as_posix(),
                    'source_root':trusted.relative_to(ROOT).as_posix(), 'printed_roots':[]}]}
out = HERE/'trusted-setup-gate.json'
with out.open('x',encoding='utf-8',newline='\n') as stream:
    json.dump(gate,stream,indent=2);stream.write('\n')
print(json.dumps({'path':out.relative_to(ROOT).as_posix(),'sha256':sha(out)}))
