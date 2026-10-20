"""One fixed official release-asset fetch after GitHub metadata rate limiting.

The expected digest/size are frozen in the already archived official release
provenance. This fetch does not claim a fresh release-metadata query, and never
executes the downloaded archive or any compiler.
"""
import datetime
import hashlib
import json
import os
from pathlib import Path
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
OUT = ROOT / 'tmp/w9a2-20261020/linux-setup-v0'
NAME = 'lean-4.33.0-rc2-linux.tar.zst'
URL = 'https://github.com/leanprover/lean4/releases/download/v4.33.0-rc2/' + NAME
SHA = '48010c7d6264dc992574e9b0e09ece1f9c648e8f5106066b2cdb6834a6a60a6c'
SIZE = 574905502

provenance = ROOT / 'verification/gram-defect-20261015/setup/runtime.json'
old = json.loads(provenance.read_text(encoding='utf-8'))
assert old['compiler_archive_sha256'] == SHA
assert old['lean_sha256'] == 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
OUT.mkdir(parents=True, exist_ok=True)
dest = OUT / NAME
partial = OUT / (NAME + '.direct-v1.part')
assert not dest.exists() and not partial.exists()
hasher = hashlib.sha256()
total = 0
with urllib.request.urlopen(URL, timeout=120) as response, partial.open('xb') as stream:
    status, headers, final_url = response.status, dict(response.headers), response.url
    while block := response.read(1024 * 1024):
        total += len(block)
        assert total <= SIZE
        hasher.update(block)
        stream.write(block)
    stream.flush()
    os.fsync(stream.fileno())
assert total == SIZE and hasher.hexdigest() == SHA
partial.rename(dest)
receipt = {'status': 'PASS_DOWNLOAD_ONLY', 'http_status': status, 'url': URL,
           'resolved_url': final_url, 'headers': headers,
           'retrieved_UTC': datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'bytes': total, 'sha256': hasher.hexdigest(),
           'fresh_release_metadata_queried': False,
           'expected_digest_provenance': str(provenance.relative_to(ROOT)),
           'provenance_sha256': hashlib.sha256(provenance.read_bytes()).hexdigest(),
           'compiler_invocations': 0, 'proof_invocations': 0}
with (OUT / 'download-receipt.json').open('x', encoding='utf-8', newline='\n') as stream:
    json.dump(receipt, stream, indent=2)
    stream.write('\n')
    stream.flush()
    os.fsync(stream.fileno())
print(json.dumps({'status': receipt['status'], 'bytes': total, 'sha256': SHA}))
