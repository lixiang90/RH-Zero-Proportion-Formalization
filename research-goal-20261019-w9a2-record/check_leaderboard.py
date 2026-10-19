"""One fresh public leaderboard snapshot for this analysis."""
import datetime
import hashlib
import json
import pathlib
import time
import urllib.request

root = pathlib.Path(__file__).resolve().parent
url = 'https://www.riemannzeta.fun/api/leaderboard?w9a2analysis=' + str(time.time_ns())
request = urllib.request.Request(url, headers={'Cache-Control': 'no-cache'})
with urllib.request.urlopen(request, timeout=60) as response:
    data = response.read(1000001)
    assert len(data) <= 1000000
    headers = dict(response.headers)
    status = response.status
obj = json.loads(data)
out = root / 'leaderboard.json'
with out.open('xb') as stream:
    stream.write(data)
receipt = {'retrievedAt': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'url': url, 'status': status, 'headers': headers, 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
with (root / 'leaderboard-receipt.json').open('x', encoding='utf-8') as stream:
    json.dump(receipt, stream, indent=2)
    stream.write('\n')
print(json.dumps({'receipt': receipt, 'data': obj}, ensure_ascii=False))
