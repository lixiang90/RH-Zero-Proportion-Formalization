"""Stage only the hash-pinned W9A2 analysis checkpoint and prepare API blobs."""
from pathlib import Path
from hashlib import sha256
import base64
import json
import subprocess

ROOT = Path(__file__).resolve().parent.parent
HERE = Path(__file__).resolve().parent
TMP = ROOT / 'tmp' / 'w9a2-sync'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

def main():
    checkpoint = HERE / 'checkpoint-files.json'
    manifest = json.loads(checkpoint.read_bytes())
    expected = dict(manifest['files'])
    expected[checkpoint.relative_to(ROOT).as_posix()] = {'bytes': checkpoint.stat().st_size, 'sha256': sha256(checkpoint.read_bytes()).hexdigest()}
    assert not git('diff', '--cached', '--name-only'), 'preserve existing staged changes'
    for rel, row in expected.items():
        raw = (ROOT / rel).read_bytes()
        assert len(raw) == row['bytes'] and sha256(raw).hexdigest() == row['sha256'], rel
    parent = git('rev-parse', 'HEAD').decode().strip()
    assert parent == '91972e71dae635e719eea29b24a2c0150bf3e510'
    TMP.mkdir(parents=True, exist_ok=True)
    pathspec = TMP / 'pathspec.txt'
    pathspec.write_text('\n'.join(sorted(expected)) + '\n', encoding='utf-8')
    subprocess.run(['git', 'add', '-f', '--pathspec-from-file=' + str(pathspec)], cwd=ROOT, check=True)
    changed = git('diff', '--cached', '--name-only', '-z').decode().split('\0')[:-1]
    assert set(changed) <= set(expected)
    index = {}
    for line in git('ls-files', '--stage', '-z').split(b'\0'):
        if not line:
            continue
        head, path = line.split(b'\t', 1)
        mode, oid, stage = head.decode().split()
        assert stage == '0'
        index[path.decode()] = (mode, oid)
    parent_blobs = {line.split()[2].decode() for line in git('ls-tree', '-r', 'HEAD').splitlines() if line.split()[1] == b'blob'}
    entries = []
    blobs = {}
    for rel in changed:
        mode, oid = index[rel]
        raw = git('show', ':' + rel)
        assert len(raw) == expected[rel]['bytes'] and sha256(raw).hexdigest() == expected[rel]['sha256'], rel
        entries.append({'path': rel, 'mode': mode, 'type': 'blob', 'sha': oid})
        if oid not in parent_blobs:
            blobs[oid] = {'sha': oid, 'bytes': len(raw), 'encoding': 'base64', 'content': base64.b64encode(raw).decode(), 'example_path': rel}
    plan = {'parent': parent, 'base_tree': git('rev-parse', 'HEAD^{tree}').decode().strip(), 'tree': git('write-tree').decode().strip(), 'entries': entries, 'blobs': list(blobs.values())}
    (TMP / 'plan.json').write_text(json.dumps(plan, separators=(',', ':')), encoding='utf-8')
    print(json.dumps({'parent': parent, 'tree': plan['tree'], 'changed': len(entries), 'new_blobs': len(blobs), 'bytes': sum(x['bytes'] for x in blobs.values())}, indent=2))

if __name__ == '__main__':
    main()
