from pathlib import Path
from urllib.request import Request, urlopen
from datetime import datetime, timezone
import hashlib
import json

root = Path(__file__).resolve().parents[1]
commit = 'cb7558bc2944358366b5aac4d187f3b3ee5a637c'
relative = 'submission/w9a2-weighted-potential-20261020-prepared-v7/proof/Solution.lean'
url = f'https://raw.githubusercontent.com/lixiang90/RH-Zero-Proportion-Formalization/{commit}/{relative}'
expected = 'dae01f6844642d7f9ee8180616c1f57aefc18ab8616bc8a4a46a14bf8e9fefc6'
with urlopen(Request(url, headers={'User-Agent':'RH-Zero-Proportion-Formalization/source-byte-audit'}), timeout=45) as response:
    raw = response.read()
    status = response.status
    etag = response.headers.get('ETag')
assert status == 200
assert len(raw) == 1829242 and hashlib.sha256(raw).hexdigest() == expected
assert raw == (root / relative).read_bytes()
receipt = {
 'schema': 'fixed-pushed-v7-source-byte-check-v1',
 'observed_UTC': datetime.now(timezone.utc).isoformat(),
 'commit': commit,
 'public_fixed_url': url,
 'HTTP_status': status,
 'ETag': etag,
 'bytes': len(raw),
 'sha256': expected,
 'remote_bytes_equal_prepared_local_source': True,
 'actual_normal_git_push_exit_code': 0,
 'push_tool_chunk': '3759a9',
 'scope': 'One exact fixed-commit public source fetch and successful push; not a new full-tree audit, compilation or official acceptance',
}
output = Path(__file__).with_name('receipt.json')
assert not output.exists()
output.write_bytes((json.dumps(receipt, indent=2) + '\n').encode('utf-8'))
print(json.dumps(receipt))
