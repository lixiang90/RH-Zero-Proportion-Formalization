"""Archive one new read-only record check in a caller-named fresh directory."""
import argparse
import datetime
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import time
import urllib.request

ap = argparse.ArgumentParser()
ap.add_argument('--directory', required=True)
args = ap.parse_args()
HERE = Path(__file__).resolve().parent
dest = (HERE / args.directory).resolve()
assert dest.is_relative_to(HERE) and not dest.exists()
url = 'https://www.riemannzeta.fun/api/leaderboard?w9a2proof=' + str(time.time_ns())
with urllib.request.urlopen(urllib.request.Request(url, headers={'Cache-Control': 'no-cache'}), timeout=45) as response:
    raw = response.read(1000001)
    assert len(raw) <= 1000000
    receipt = {'retrievedAt': datetime.datetime.now(datetime.timezone.utc).isoformat(),
               'url': url, 'status': response.status, 'headers': dict(response.headers),
               'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}
data = json.loads(raw)
score = lambda row: Fraction(int(row['exactRational']['numerator']), int(row['exactRational']['denominator']))
eligible = [row for row in data['records'] if row['status'] == 'kernel-verified'
            and row['track'] == 'critical-line' and row.get('exactRational')]
current = max(eligible, key=score)
candidate = Fraction(3337881639516708570682858853672166187793,
                     4955348542279967171490000000000000000000)
dest.mkdir()
(dest / 'leaderboard.json').write_bytes(raw)
(dest / 'leaderboard-receipt.json').write_bytes((json.dumps(receipt, indent=2) + '\n').encode())
print(json.dumps({'current': current['id'], 'R': str(score(current)),
                  'candidate_strictly_above_current': candidate > score(current),
                  'receipt': receipt}, ensure_ascii=True))
assert candidate > score(current), 'Current record changed: route review is required before candidate execution'
