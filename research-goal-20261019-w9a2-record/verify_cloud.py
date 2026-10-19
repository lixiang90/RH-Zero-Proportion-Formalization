"""Read-only complete tree/ref and selected raw-byte checks after publication."""
from pathlib import Path
from hashlib import sha256
import json
import subprocess
import sys
import urllib.request

ROOT = Path(__file__).resolve().parent.parent
API = 'https://api.github.com/repos/lixiang90/RH-Zero-Proportion-Formalization'
commit, expected_tree = sys.argv[1:3]

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

def fetch(url):
    req = urllib.request.Request(url, headers={'User-Agent': 'RH-Zero-W9A2-analysis-verifier', 'Cache-Control': 'no-cache'})
    with urllib.request.urlopen(req, timeout=60) as response:
        return response.read()

local = {}
for row in git('ls-tree', '-r', '--full-tree', '-z', commit).split(b'\0'):
    if not row:
        continue
    head, path = row.split(b'\t', 1)
    mode, kind, oid = head.decode().split()
    local[path.decode()] = (mode, kind, oid)
tree = json.loads(fetch(API + '/git/trees/' + expected_tree + '?recursive=1'))
assert tree['sha'] == expected_tree and not tree['truncated']
remote = {x['path']: (x['mode'], x['type'], x['sha']) for x in tree['tree'] if x['type'] != 'tree'}
differences = [p for p in sorted(local.keys() | remote.keys()) if local.get(p) != remote.get(p)]
assert not differences
head = json.loads(fetch(API + '/git/ref/heads/main'))['object']['sha']
refs = {r: git('rev-parse', r).decode().strip() for r in ['HEAD', 'origin/main']}
assert head == commit and all(v == commit for v in refs.values())
raw_checks = []
for rel in ['research-goal-20261019-w9a2-record/ANALYSIS.zh.md', 'research-goal-20261019-w9a2-weighted-graph/weighted-graph.json', 'research-goal-20261019-w9a2-record/official/proof/Solution.lean', 'submission/single-exception-overlap-accepted-20261019/proof/Solution.lean']:
    data = fetch('https://raw.githubusercontent.com/lixiang90/RH-Zero-Proportion-Formalization/' + commit + '/' + rel)
    assert data == (ROOT / rel).read_bytes()
    raw_checks.append({'path': rel, 'bytes': len(data), 'sha256': sha256(data).hexdigest()})
old_proof = git('show', '91972e71dae635e719eea29b24a2c0150bf3e510:submission/single-exception-overlap-accepted-20261019/proof/Solution.lean')
assert old_proof == (ROOT / 'submission/single-exception-overlap-accepted-20261019/proof/Solution.lean').read_bytes()
receipt = {'commit': commit, 'tree': expected_tree, 'complete_local_blob_count': len(local), 'complete_remote_blob_count': len(remote), 'differences': differences, 'public_main': head, 'local_refs': refs, 'raw_checks': raw_checks, 'prior_accepted_proof_unchanged': True, 'new_candidate_formalized': False, 'new_candidate_website_ready': False}
out = ROOT / 'tmp' / 'w9a2-sync' / 'cloud-receipt.json'
with out.open('x', encoding='utf-8') as stream:
    json.dump(receipt, stream, indent=2)
    stream.write('\n')
print(json.dumps(receipt, indent=2))
