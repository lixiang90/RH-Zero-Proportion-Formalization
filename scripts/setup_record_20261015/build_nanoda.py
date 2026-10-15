"""Build the exact pinned nanoda source and Cargo.lock with verified local Rust components."""
import argparse
from pathlib import Path
import hashlib
import json
import os
import subprocess
import time

REPOSITORY = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--setup-dir', type=Path, default=REPOSITORY / 'tmp/setup-20261015')
args = parser.parse_args()
ARCHIVES = args.setup_dir.resolve()
RUNTIME = json.loads((ARCHIVES / 'runtime.json').read_text())
ROOT = Path(RUNTIME['runtime_root'])
RUST = ROOT / 'rust'
receipts = json.loads((ARCHIVES / 'rust-sources.json').read_text())
for entry in receipts:
    name = entry['url'].rsplit('/',1)[-1]
    archive = ARCHIVES / name
    assert hashlib.sha256(archive.read_bytes()).hexdigest() == entry['sha256']
    folder = ROOT / name.removesuffix('.tar.xz')
    if not folder.exists():
        subprocess.run(['tar', '-xJf', str(archive), '-C', str(ROOT)], check=True)
    subprocess.run([str(folder/'install.sh'), '--prefix='+str(RUST), '--disable-ldconfig'], check=True,
                   stdout=subprocess.DEVNULL)

NANODA = Path(RUNTIME['package_root']) / 'nanoda'
ENV = dict(os.environ, PATH=str(RUST/'bin')+':'+os.environ['PATH'],
           CARGO_HOME=str(ROOT/'cargo'), CARGO_TARGET_DIR=str(ROOT/'nanoda-target'))
command = [str(RUST/'bin/cargo'), 'build', '--locked', '--release', '--bin', 'nanoda_bin']
started = time.monotonic()
log = ROOT/'nanoda-build.log'
with log.open('wb') as out:
    process = subprocess.run(command, cwd=NANODA, env=ENV, stdout=out, stderr=subprocess.STDOUT)
binary = ROOT/'nanoda-target/release/nanoda_bin'
record = {'command': command, 'working_directory': str(NANODA), 'exit_code': process.returncode,
          'elapsed_seconds': time.monotonic()-started, 'source_commit': '418320295890faed83a96fd97907b12a3b6728c2',
          'rust_components': receipts, 'rustc_version': subprocess.check_output([str(RUST/'bin/rustc'),'--version'],text=True).strip(),
          'cargo_lock_sha256': hashlib.sha256((NANODA/'Cargo.lock').read_bytes()).hexdigest(),
          'binary': str(binary), 'binary_sha256': hashlib.sha256(binary.read_bytes()).hexdigest() if binary.exists() else None,
          'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest(), 'log': str(log)}
source = next(entry for entry in RUNTIME['source_archives'] if entry['name'] == 'nanoda')
record.update({'source_archive_sha256': source['archive_sha256'], 'build_command': command,
               'source_archive_url': source['url']})
(ARCHIVES/'nanoda-build.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record, indent=2), flush=True)
assert process.returncode == 0
