"""Read-only full Git tree comparison plus fresh public critical-source GETs."""
import argparse
import datetime
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time
import urllib.parse
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
ap = argparse.ArgumentParser()
ap.add_argument('--commit', required=True)
ap.add_argument('--directory', required=True)
ap.add_argument('--critical', action='append', default=[])
args = ap.parse_args()
assert re.fullmatch('[0-9a-f]{40}', args.commit)
dest = (ROOT / args.directory).resolve()
assert dest.is_relative_to(ROOT) and not dest.exists()


def git(*argv):
    return subprocess.check_output(['git', *argv], cwd=ROOT)


def gh(endpoint):
    return subprocess.check_output(['gh', 'api', endpoint], cwd=ROOT)


repository = 'lixiang90/RH-Zero-Proportion-Formalization'
assert git('remote', 'get-url', 'origin').decode().strip() == 'https://github.com/' + repository + '.git'
branch = json.loads(gh('repos/' + repository + '/branches/main'))
assert branch['commit']['sha'] == args.commit
tree_id = git('rev-parse', args.commit + '^{tree}').decode().strip()
raw_tree = gh('repos/' + repository + '/git/trees/' + tree_id + '?recursive=1')
remote = json.loads(raw_tree)
assert remote.get('truncated') is False
local = {}
for row in git('ls-tree', '-r', '-z', args.commit).split(b'\0'):
    if row:
        metadata, raw_path = row.split(b'\t', 1)
        mode, kind, oid = metadata.decode().split()
        assert kind == 'blob', (kind, raw_path)
        local[raw_path.decode('utf-8')] = {'mode': mode, 'type': kind, 'sha': oid}
public = {row['path']: {key: row[key] for key in ['mode', 'type', 'sha']}
          for row in remote['tree'] if row['type'] != 'tree'}
assert local == public, 'Local commit and full GitHub tree differ'
assert remote['sha'] == tree_id
critical = []
for name in args.critical:
    assert name in local
    source = git('show', args.commit + ':' + name)
    url = ('https://raw.githubusercontent.com/' + repository + '/' + args.commit + '/' +
           urllib.parse.quote(name, safe='/') + '?w9a2sync=' + str(time.time_ns()))
    with urllib.request.urlopen(urllib.request.Request(url, headers={'Cache-Control': 'no-cache'}), timeout=60) as response:
        data = response.read(5000001)
        status, headers = response.status, dict(response.headers)
    assert len(data) <= 5000000 and status == 200 and data == source, name
    critical.append({'path': name, 'url': url, 'HTTP': status, 'headers': headers,
                     'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(),
                     'public_raw_equals_exact_local_commit_blob': True})
dest.mkdir()
(dest / 'github-full-tree.json.gz').write_bytes(gzip.compress(raw_tree, mtime=0))
result = {'passed': True, 'scope': 'One exact commit and its full public Git tree. No final proof/website acceptance claim.',
          'checked_UTC': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'repository': repository, 'commit': args.commit, 'tree': tree_id,
          'GitHub_main_commit': branch['commit']['sha'], 'complete_blob_count': len(local),
          'blob_or_mode_differences': 0, 'GitHub_API_tree_truncated': False,
          'critical_public_raw_GETs': critical,
          'uncommitted_work_is_outside_this_commit_audit': True}
(dest / 'audit.json').write_bytes((json.dumps(result, ensure_ascii=True, indent=2) + '\n').encode())
print(json.dumps({'passed': True, 'commit': args.commit, 'complete_blobs': len(local),
                  'differences': 0, 'critical_raw_GETs': len(critical)}))
