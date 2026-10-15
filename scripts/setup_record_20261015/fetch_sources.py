"""Fetch pinned source archives over HTTPS, with content hashes and safe extraction."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
from pathlib import Path
import tarfile
import time
import urllib.request

REPOSITORY = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--setup-dir', type=Path, default=REPOSITORY / 'tmp/setup-20261015')
args = parser.parse_args()
ROOT = args.setup_dir.resolve()
ROOT.mkdir(parents=True, exist_ok=True)
MANIFEST = json.loads((REPOSITORY / 'lake-manifest.json').read_text())
LOCK = {entry['name']: entry for entry in json.loads(Path(__file__).with_name('source-archives.lock.json').read_text())}
PACKAGES = [(p['name'], p['url'].removesuffix('.git').replace('https://github.com/', ''), p['rev'])
            for p in MANIFEST['packages']]
PACKAGES += [
    ('lean4export', 'leanprover/lean4export', 'b18d673bd29b476466a51a3be1012df2ed322b10'),
    ('Comparator', 'leanprover/comparator', '273294467ce06429e6667ece7f5699f8678c9f4e'),
    ('nanoda', 'ammkrn/nanoda_lib', '418320295890faed83a96fd97907b12a3b6728c2'),
]

def fetch(item):
    name, repo, pin = item
    url = f'https://codeload.github.com/{repo}/tar.gz/{pin}'
    archive = ROOT / (name + '.tar.gz')
    target = ROOT / 'packages' / name
    target.parent.mkdir(exist_ok=True)
    if not archive.exists():
        for attempt in range(4):
            try:
                with urllib.request.urlopen(url, timeout=60) as inp, archive.with_suffix('.part').open('wb') as out:
                    while block := inp.read(1024 * 1024):
                        out.write(block)
                archive.with_suffix('.part').replace(archive)
                break
            except Exception:
                if attempt == 3:
                    raise
                time.sleep(2)
    expected = LOCK[name]
    assert expected['commit'] == pin and expected['repository'] == repo
    assert hashlib.sha256(archive.read_bytes()).hexdigest() == expected['archive_sha256'], name
    if not (target / '.archive-extracted').exists():
        with tarfile.open(archive) as tar:
            members = tar.getmembers()
            prefix = members[0].name.split('/')[0]
            for member in members:
                parts = Path(member.name).parts
                if not parts or parts[0] != prefix or '..' in parts or member.issym() or member.islnk():
                    continue
                member.name = '/'.join(parts[1:])
                if member.name:
                    tar.extract(member, target, filter='data')
        (target / '.archive-extracted').write_text(pin + '\n')
    return {'name': name, 'repository': repo, 'commit': pin, 'url': url,
            'archive_sha256': hashlib.sha256(archive.read_bytes()).hexdigest(),
            'archive_bytes': archive.stat().st_size, 'source_path': str(target)}

if __name__ == '__main__':
    receipts = []
    with ThreadPoolExecutor(max_workers=6) as pool:
        for result in as_completed([pool.submit(fetch, item) for item in PACKAGES]):
            try:
                entry = result.result()
                receipts.append(entry)
                print(entry['name'], entry['archive_bytes'], entry['archive_sha256'], flush=True)
            except Exception as error:
                print(type(error).__name__, str(error), flush=True)
                raise
    (ROOT / 'sources.json').write_text(json.dumps(receipts, indent=2) + '\n')
