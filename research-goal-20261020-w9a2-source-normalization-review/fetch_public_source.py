"""Read-only HTTPS GET audit of the official public repository; never run its code."""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import urllib.request

HERE = Path(__file__).resolve().parent
BASE = 'https://api.github.com/repos/josusanmartin/riemann'
HEADERS = {'User-Agent': 'W9A2-official-source-normalization-read-only-audit/1.0',
           'Cache-Control': 'no-cache', 'Pragma': 'no-cache', 'Accept': 'application/vnd.github+json'}


def stamp():
    return datetime.now(timezone.utc).isoformat()


def save(relative, raw):
    item = HERE / relative; item.parent.mkdir(parents=True, exist_ok=True)
    with item.open('xb') as stream:
        stream.write(raw)


def fetch(url, relative, max_bytes=8_000_000):
    started = stamp()
    with urllib.request.urlopen(urllib.request.Request(url, headers=HEADERS), timeout=45) as response:
        raw = response.read(max_bytes + 1)
        assert response.status == 200 and len(raw) <= max_bytes
        receipt = {'started_at_utc': started, 'completed_at_utc': stamp(), 'url': url,
            'final_url': response.url, 'status': response.status, 'headers': dict(response.headers),
            'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}
    save(relative, raw)
    save(relative + '.http.json', (json.dumps(receipt, ensure_ascii=False, indent=2) + '\n').encode())
    return raw, receipt


def main():
    ref, _ = fetch(BASE + '/git/ref/heads/main', 'head-before.json')
    commit_sha = json.loads(ref)['object']['sha']
    commit_raw, _ = fetch(BASE + '/git/commits/' + commit_sha, 'commit.json')
    tree_sha = json.loads(commit_raw)['tree']['sha']
    tree_raw, _ = fetch(BASE + '/git/trees/' + tree_sha + '?recursive=1', 'tree.json')
    tree = json.loads(tree_raw); assert not tree['truncated']
    selected = [r for r in tree['tree'] if r['type'] == 'blob' and
        ((r['path'].startswith('src/') and r['path'].endswith(('.ts', '.tsx'))) or
         r['path'] in ['README.md', 'CONTRIBUTING.md'])]
    assert 1 <= len(selected) <= 220
    def one(entry):
        name = entry['path']
        url = 'https://raw.githubusercontent.com/josusanmartin/riemann/' + commit_sha + '/' + name
        raw, receipt = fetch(url, 'source/' + name, 2_000_000)
        blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        assert blob == entry['sha'] and len(raw) == entry['size'], name
        return {'path': name, 'git_blob_sha1': blob, 'sha256': receipt['sha256'], 'bytes': len(raw),
                'immutable_source_url': url}
    with ThreadPoolExecutor(max_workers=4) as pool:
        sources = list(pool.map(one, selected))
    after_raw, _ = fetch(BASE + '/git/ref/heads/main', 'head-after.json')
    after_sha = json.loads(after_raw)['object']['sha']
    report = {'scope': 'Read-only current public-main source snapshot; no website submission or code execution',
        'commit_sha': commit_sha, 'tree_sha': tree_sha, 'head_after_sha': after_sha,
        'HEAD_stable_during_capture': commit_sha == after_sha, 'sources': sources,
        'source_files_captured': len(sources), 'HTTP_methods': ['GET'], 'proof_or_website_write_calls': 0}
    save('capture.json', (json.dumps(report, ensure_ascii=False, indent=2) + '\n').encode())
    print(json.dumps({'commit_sha': commit_sha, 'head_after_sha': after_sha,
        'HEAD_stable_during_capture': commit_sha == after_sha, 'source_files': len(sources),
        'proof_or_website_write_calls': 0}), flush=True)


if __name__ == '__main__':
    main()
