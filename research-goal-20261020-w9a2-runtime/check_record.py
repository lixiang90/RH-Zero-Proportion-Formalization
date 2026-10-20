"""Archive one fresh leaderboard response without touching frozen snapshots."""
import datetime
import hashlib
import json
from pathlib import Path
import time
import urllib.request

HERE = Path(__file__).resolve().parent
url = 'https://www.riemannzeta.fun/api/leaderboard?w9a2continuation=' + str(time.time_ns())
request = urllib.request.Request(url, headers={'Cache-Control': 'no-cache'})
with urllib.request.urlopen(request, timeout=45) as response:
    raw = response.read(1000001)
    assert len(raw) <= 1000000
    receipt = {'retrievedAt': datetime.datetime.now(datetime.timezone.utc).isoformat(),
               'url': url, 'status': response.status, 'headers': dict(response.headers),
               'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}
data = json.loads(raw)
with (HERE / 'leaderboard.json').open('xb') as stream:
    stream.write(raw)
with (HERE / 'leaderboard-receipt.json').open('x', encoding='utf-8') as stream:
    json.dump(receipt, stream, indent=2)
    stream.write('\n')
print(json.dumps({'receipt': receipt, 'data': data}, ensure_ascii=False))
