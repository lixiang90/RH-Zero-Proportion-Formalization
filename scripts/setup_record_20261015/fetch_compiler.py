"""Fetch the exact official Linux Lean release without installing a system toolchain."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import urllib.request

REPOSITORY = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--setup-dir', type=Path, default=REPOSITORY / 'tmp/setup-20261015')
args = parser.parse_args()
setup = args.setup_dir.resolve()
setup.mkdir(parents=True, exist_ok=True)
filename = 'lean-4.33.0-rc2-linux.tar.zst'
expected = '48010c7d6264dc992574e9b0e09ece1f9c648e8f5106066b2cdb6834a6a60a6c'
metadata_url = 'https://api.github.com/repos/leanprover/lean4/releases/tags/v4.33.0-rc2'
with urllib.request.urlopen(metadata_url, timeout=60) as response:
    metadata = json.loads(response.read())
(setup / 'lean-release.json').write_text(json.dumps(metadata, indent=2) + '\n')
asset = next(item for item in metadata['assets'] if item['name'] == filename)
assert asset['digest'] == 'sha256:' + expected
assert asset['size'] == 574905502
target = setup / filename

def digest(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            hasher.update(block)
    return hasher.hexdigest()

if not target.exists() or digest(target) != expected:
    partial = target.with_suffix(target.suffix + '.part')
    if os.name == 'nt':
        shell = shutil.which('pwsh') or shutil.which('powershell')
        if not shell:
            raise RuntimeError('PowerShell is required for the Windows HTTPS download route')
        # Single-quoted PowerShell strings do not interpolate variables or backticks.
        quoted_url = "'" + asset['browser_download_url'].replace("'", "''") + "'"
        quoted_target = "'" + str(partial).replace("'", "''") + "'"
        command = "$ProgressPreference = 'SilentlyContinue'; Invoke-WebRequest -Uri " + quoted_url + ' -OutFile ' + quoted_target
        subprocess.run([shell, '-NoProfile', '-NonInteractive', '-Command', command], check=True)
    else:
        with urllib.request.urlopen(asset['browser_download_url'], timeout=90) as response, partial.open('wb') as out:
            while block := response.read(1024 * 1024):
                out.write(block)
    assert partial.stat().st_size == asset['size'] and digest(partial) == expected
    partial.replace(target)
assert target.stat().st_size == asset['size'] and digest(target) == expected
print(json.dumps({'archive': str(target), 'bytes': target.stat().st_size, 'sha256': expected,
                  'official_metadata': str(setup/'lean-release.json')}, indent=2))
