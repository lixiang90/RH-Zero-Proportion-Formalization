"""Fetch exact Rust components and verify the official component digests."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import hashlib
import urllib.request
import json

REPOSITORY = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--setup-dir', type=Path, default=REPOSITORY / 'tmp/setup-20261015')
args = parser.parse_args()
ROOT = args.setup_dir.resolve()
ROOT.mkdir(parents=True, exist_ok=True)

def fetch(component):
    name = f'{component}-1.85.1-x86_64-unknown-linux-gnu.tar.xz'
    url = 'https://static.rust-lang.org/dist/' + name
    target = ROOT / name
    with urllib.request.urlopen(url + '.sha256', timeout=40) as response:
        expected = response.read().decode().split()[0]
    if not target.exists():
        with urllib.request.urlopen(url, timeout=60) as response, target.open('wb') as out:
            while chunk := response.read(1024 * 1024):
                out.write(chunk)
    observed = hashlib.sha256(target.read_bytes()).hexdigest()
    assert observed == expected, (component, observed, expected)
    print(component, target.stat().st_size, observed, flush=True)
    return {'component': component, 'version': '1.85.1', 'url': url, 'sha256': observed}

with ThreadPoolExecutor(max_workers=3) as pool:
    receipts = list(pool.map(fetch, ['cargo', 'rustc', 'rust-std']))
(ROOT / 'rust-sources.json').write_text(json.dumps(receipts, indent=2) + '\n')
