"""Pinned setup only: official Linux compiler plus existing data-only libraries.

This program NEVER invokes lean/lake/compiler/cache commands. The two phases
must be separately authorized by the root owner. A later trusted-import gate
is necessary to test portability; no imported artifact is thereby re-proved.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import os
import platform
import shutil
import subprocess
import time
import urllib.request

REPO = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
ARCHIVES = REPO / 'tmp/w9a2-20261020/linux-setup-v0'
LINUX_ROOT = Path('/var/tmp/rh-zero-w9a2-20261020/runtime-v0')
ASSET = 'lean-4.33.0-rc2-linux.tar.zst'
ASSET_SHA = '48010c7d6264dc992574e9b0e09ece1f9c648e8f5106066b2cdb6834a6a60a6c'
ASSET_SIZE = 574905502
ELF_SHA = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
RELEASE = 'https://api.github.com/repos/leanprover/lean4/releases/tags/v4.33.0-rc2'
SOURCE_LOCK = REPO / 'scripts/setup_record_20261015/source-archives.lock.json'
MANIFEST = REPO / 'lake-manifest.json'
GIT_ENV = dict(os.environ, GIT_NO_LAZY_FETCH='1', GIT_OPTIONAL_LOCKS='0')
DATA_SUFFIXES = ('.olean', '.olean.server', '.olean.private', '.ir', '.ir.sig',
                 '.olean.hash', '.olean.server.hash', '.olean.private.hash',
                 '.ir.hash', '.ir.sig.hash', '.trace')


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def write_json(path, value):
    with Path(path).open('x', encoding='utf-8') as f:
        json.dump(value, f, ensure_ascii=False, indent=2)
        f.write('\n')
        f.flush()
        os.fsync(f.fileno())


def pins():
    lock = {e['name']: e for e in json.loads(SOURCE_LOCK.read_text(encoding='utf-8'))}
    entries = json.loads(MANIFEST.read_text(encoding='utf-8'))['packages']
    assert len(entries) == 10
    result = []
    for e in entries:
        p = lock[e['name']]
        assert p['commit'] == e['rev']
        assert e['url'].removesuffix('.git') == 'https://github.com/' + p['repository']
        result.append(p)
    return result


def fetch():
    ARCHIVES.mkdir(parents=True, exist_ok=True)
    target = ARCHIVES / ASSET
    if target.exists():
        assert target.stat().st_size == ASSET_SIZE and sha(target) == ASSET_SHA
        raise RuntimeError('Valid existing archive retained; no duplicate download. Root must select mirror phase.')
    with urllib.request.urlopen(RELEASE, timeout=60) as f:
        metadata_bytes = f.read()
    metadata = json.loads(metadata_bytes)
    item = next(a for a in metadata['assets'] if a['name'] == ASSET)
    assert item['size'] == ASSET_SIZE and item['digest'] == 'sha256:' + ASSET_SHA
    assert item['browser_download_url'] == ('https://github.com/leanprover/lean4/releases/download/'
                                             'v4.33.0-rc2/' + ASSET)
    # Fresh named directory/one attempt; retain partial/failure rather than retry.
    (ARCHIVES / 'release.json').write_bytes(metadata_bytes)
    partial = ARCHIVES / (ASSET + '.part')
    with urllib.request.urlopen(item['browser_download_url'], timeout=120) as inp, partial.open('xb') as out:
        while chunk := inp.read(1024 * 1024):
            out.write(chunk)
        out.flush()
        os.fsync(out.fileno())
    assert partial.stat().st_size == ASSET_SIZE and sha(partial) == ASSET_SHA
    partial.rename(target)
    write_json(ARCHIVES / 'download-receipt.json', {
        'status': 'PASS_DOWNLOAD_ONLY', 'archive': str(target), 'bytes': ASSET_SIZE,
        'sha256': ASSET_SHA, 'official_release_url': RELEASE,
        'release_metadata_sha256': hashlib.sha256(metadata_bytes).hexdigest(),
        'compiler_invocations': 0, 'proof_invocations': 0,
    })


def mirror():
    assert os.name == 'posix' and platform.machine() == 'x86_64'
    assert str(REPO).startswith('/mnt/e/codex-build/RH-Zero-Proportion-Formalization')
    assert LINUX_ROOT == Path('/var/tmp/rh-zero-w9a2-20261020/runtime-v0')
    assert not LINUX_ROOT.exists(), 'Never overwrite a prior runtime; preserve it and request a new root gate.'
    assert shutil.disk_usage('/var/tmp').free >= 15 * 1024**3
    archive = ARCHIVES / ASSET
    assert archive.stat().st_size == ASSET_SIZE and sha(archive) == ASSET_SHA
    package_pins = pins()
    heads = {}
    # Git is only a source-identity reader. No checkout/fetch/build/submodule.
    for e in package_pins:
        source = REPO / '.lake/packages' / e['name']
        head = subprocess.check_output(['git', '-c', 'safe.directory=' + str(source),
            '-C', str(source), 'rev-parse', 'HEAD'], text=True, env=GIT_ENV).strip()
        assert head == e['commit'], e['name']
        heads[e['name']] = head
    names = subprocess.check_output(['tar', '--zstd', '-tf', str(archive)], text=True).splitlines()
    for name in names:
        pp = PurePosixPath(name)
        assert not pp.is_absolute() and '..' not in pp.parts
        assert pp.parts and pp.parts[0] == 'lean-4.33.0-rc2-linux'
    LINUX_ROOT.mkdir(parents=True, exist_ok=False)
    subprocess.run(['tar', '--zstd', '-xf', str(archive), '-C', str(LINUX_ROOT)], check=True)
    lean = LINUX_ROOT / 'lean-4.33.0-rc2-linux/bin/lean'
    assert sha(lean) == ELF_SHA
    journal = LINUX_ROOT / 'mirror-files.jsonl'
    totals = {'sources': 0, 'source_bytes': 0, 'library_data': 0, 'library_bytes': 0}
    skipped_source_symlinks = []

    def record_copy(src, dst, kind, git_oid=None):
        assert src.is_file() and not src.is_symlink()
        dst.parent.mkdir(parents=True, exist_ok=True)
        expected = sha(src)
        if git_oid:
            raw = src.read_bytes()
            blob = b'blob ' + str(len(raw)).encode() + b'\0' + raw
            # Autocrlf is acceptable only for text source/config files; copy the
            # canonical tracked bytes to Linux, binding them to the pinned blob.
            if hashlib.sha1(blob).hexdigest() != git_oid:
                raw = raw.replace(b'\r\n', b'\n')
                blob = b'blob ' + str(len(raw)).encode() + b'\0' + raw
            assert hashlib.sha1(blob).hexdigest() == git_oid, str(src)
            dst.write_bytes(raw)
        else:
            shutil.copyfile(src, dst)
            assert sha(dst) == expected
        assert sha(src) == expected, 'Input changed while copied: ' + str(src)
        item = {'kind': kind, 'source': str(src), 'destination': str(dst),
                'source_sha256': expected, 'destination_sha256': sha(dst),
                'bytes': dst.stat().st_size, 'git_blob': git_oid}
        with journal.open('a', encoding='utf-8') as out:
            out.write(json.dumps(item, ensure_ascii=False) + '\n')
        totals['sources' if kind == 'source' else 'library_data'] += 1
        totals['source_bytes' if kind == 'source' else 'library_bytes'] += item['bytes']

    packages = LINUX_ROOT / '.lake/packages'
    for e in package_pins:
        name = e['name']
        src = REPO / '.lake/packages' / name
        dst = packages / name
        tree = subprocess.check_output(['git', '-c', 'safe.directory=' + str(src),
            '-C', str(src), 'ls-tree', '-rz', 'HEAD'], env=GIT_ENV)
        for entry in tree.split(b'\0'):
            if not entry:
                continue
            meta, raw_path = entry.split(b'\t', 1)
            mode, typ, oid = meta.decode().split()
            rel = PurePosixPath(raw_path.decode())
            assert typ == 'blob' and mode in ['100644', '100755', '120000'], str(rel)
            assert not rel.is_absolute() and '..' not in rel.parts
            if mode == '120000':
                # Three tracked doc/benchmark helper links are not Lean imports.
                # Avoid dereferencing source links or fetching missing promisor
                # blobs. A new Lean/config symlink requires a reviewed revision.
                allowed = {
                    ('batteries', 'docs/README.md'),
                    ('mathlib', 'scripts/bench/build/fake-root/bin/lean.py'),
                    ('mathlib', 'scripts/bench/size/run.py'),
                }
                assert (name, str(rel)) in allowed
                skipped_source_symlinks.append({'package': name, 'path': str(rel), 'git_blob': oid})
                continue
            if rel.suffix != '.lean' and str(rel) not in {
                    'lakefile.toml', 'lean-toolchain', 'lake-manifest.json', 'LICENSE', 'NOTICE'}:
                continue
            record_copy(src / str(rel), dst / str(rel), 'source', oid)
        lib = src / '.lake/build/lib/lean'
        for directory, dirs, filenames in os.walk(lib, followlinks=False):
            dirs.sort()
            for filename in sorted(filenames):
                if not filename.endswith(DATA_SUFFIXES):
                    continue
                path = Path(directory) / filename
                rel = path.relative_to(lib)
                # Trusted ChallengeDeps is built in a separate gate; exclude
                # historical root copies and any candidate outputs.
                if name == 'Zeta23' and rel.parts[0] != 'Zeta23':
                    continue
                record_copy(path, dst / '.lake/build/lib/lean' / rel, 'library_data')
        print(json.dumps({'copied_package': name, 'totals': totals}), flush=True)
    for name in ['mathlib', 'Zeta23']:
        links = packages / name / '.lake/packages'
        links.mkdir(parents=True, exist_ok=True)
        for e in package_pins:
            if e['name'] != name:
                (links / e['name']).symlink_to(packages / e['name'], target_is_directory=True)
    runtime = {
        'status': 'SETUP_ONLY_PORTABILITY_UNTESTED', 'runtime_root': str(LINUX_ROOT),
        'lean': str(lean), 'lean_sha256': ELF_SHA, 'compiler_archive_sha256': ASSET_SHA,
        'lean_path': ':'.join(str(packages / e['name'] / '.lake/build/lib/lean') for e in package_pins),
        'package_source_pins': package_pins, 'source_git_heads': heads,
        'source_identity': 'Each canonical file verified against the pinned Git tree blob; no checkout modification.',
        'libraries': 'Byte-identical existing Windows data files only; portability not assumed proved.',
        'native_windows_binaries_copied': False, 'lake_or_setup_plugins_used': False,
        'mirror_manifest': str(journal), 'mirror_manifest_sha256': sha(journal), 'totals': totals,
        'skipped_nonimport_source_symlinks': skipped_source_symlinks,
        'compiler_invocations': 0, 'cache_invocations': 0, 'proof_invocations': 0,
        'requires_next_gate': 'After Windows original handle is terminal, one trusted-only Linux import probe; no automatic dependency rebuild.',
    }
    write_json(LINUX_ROOT / 'runtime.json', runtime)
    write_json(ARCHIVES / 'mirror-receipt.json', runtime)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('phase', choices=['download', 'mirror'])
    args = parser.parse_args()
    started = time.monotonic()
    if args.phase == 'download':
        fetch()
    else:
        mirror()
    print(json.dumps({'phase': args.phase, 'elapsed_seconds': time.monotonic() - started,
                      'compiler_invocations': 0}), flush=True)
