"""Linux-only scratch runtime; archives and final receipts remain in the repository."""
import argparse
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

REPOSITORY = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--setup-dir', type=Path, default=REPOSITORY / 'tmp/setup-20261015')
parser.add_argument('--runtime-dir', type=Path, default=Path('/var/tmp/rh-zero-20261015'))
args = parser.parse_args()
ARCHIVES = args.setup_dir.resolve()
ROOT = args.runtime_dir.resolve()
ROOT.mkdir(parents=True, exist_ok=True)
packages = ROOT / '.lake/packages'
packages.mkdir(parents=True, exist_ok=True)
sources = json.loads((ARCHIVES / 'sources.json').read_text())
lock = {entry['name']: entry for entry in json.loads(Path(__file__).with_name('source-archives.lock.json').read_text())}
for entry in sources:
    expected = lock[entry['name']]
    assert all(entry[key] == expected[key] for key in ['repository','commit','url','archive_sha256'])
for entry in sources:
    archive = ARCHIVES / (entry['name'] + '.tar.gz')
    assert hashlib.sha256(archive.read_bytes()).hexdigest() == entry['archive_sha256']
    target = packages / entry['name']
    (target / '.lake/build/lib/lean').mkdir(parents=True, exist_ok=True)
    if not (target / '.extracted').exists():
        target.mkdir(exist_ok=True)
        subprocess.run(['tar', '-xzf', str(archive), '--strip-components=1', '-C', str(target)], check=True)
        (target / '.extracted').write_text(entry['commit'])
compiler = ROOT / 'lean-4.33.0-rc2-linux'
archive = ARCHIVES / 'lean-4.33.0-rc2-linux.tar.zst'
expected = '48010c7d6264dc992574e9b0e09ece1f9c648e8f5106066b2cdb6834a6a60a6c'
assert hashlib.sha256(archive.read_bytes()).hexdigest() == expected
if not (compiler / '.extracted').exists():
    subprocess.run(['tar', '--zstd', '-xf', str(archive), '-C', str(ROOT)], check=True)
    (compiler / '.extracted').write_text(expected)
for name in ['mathlib', 'Zeta23']:
    links = packages / name / '.lake/packages'
    links.mkdir(parents=True, exist_ok=True)
    for entry in sources:
        dep = entry['name']
        link = links / dep
        if dep != name and not link.exists():
            link.symlink_to(packages / dep, target_is_directory=True)

cache = ROOT / 'cache'
cache.mkdir(exist_ok=True)
original_cache = Path('/mnt/c/Users/ip/.cache/mathlib')
if original_cache.exists():
    count = 0
    for archive in original_cache.glob('*.ltar'):
        link = cache / archive.name
        if not link.exists():
            link.symlink_to(archive)
            count += 1
    print('Read-only ltar cache links:', count, flush=True)

lean = compiler / 'bin/lean'
runtime = {
    'lean': str(lean), 'lean_sha256': hashlib.sha256(lean.read_bytes()).hexdigest(),
    'lean_version': subprocess.check_output([str(lean), '--version'], text=True).strip(),
    'compiler_archive_sha256': expected, 'compiler_official_release_metadata': str(ARCHIVES / 'lean-release.json'),
    'runtime_root': str(ROOT), 'package_root': str(packages), 'cache': str(cache),
    'lean_path': ':'.join(str(packages / entry['name'] / '.lake/build/lib/lean') for entry in sources),
    'source_archives': sources,
    'dependency_basis': 'Pinned HTTPS GitHub source archives, SHA256-bound, freshly compiled Zeta23 and official Mathlib cache',
    'git_checkout_claimed': False,
}
(ARCHIVES / 'runtime.json').write_text(json.dumps(runtime, indent=2) + '\n')
(ROOT / 'runtime.json').write_text(json.dumps(runtime, indent=2) + '\n')
print(runtime['lean_version'], flush=True)
print('Runtime:', ROOT, flush=True)
