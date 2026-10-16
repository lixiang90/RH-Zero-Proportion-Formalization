"""Write generated Lean sources without replacing a proved or live source.

An existing PASS receipt pins the exact source bytes, including proof code.
Use a new module name for a changed proof after it has been accepted.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent.parent
HERE = ROOT / 'research-goal-20261016'


def write_lean(path, body):
    path = Path(path)
    relative = path.resolve().relative_to(ROOT.resolve())
    module = '.'.join(relative.with_suffix('').parts)
    raw = body.encode('utf8')
    current = path.read_bytes() if path.exists() else None
    receipt_path = HERE / 'lean_verification.json'
    if receipt_path.exists():
        records = json.loads(receipt_path.read_bytes())['modules']
        receipt = next((r for r in records if r['module'] == module), None)
        if receipt and receipt.get('passed'):
            expected = receipt['source_sha256']
            if hashlib.sha256(raw).hexdigest() != expected:
                raise RuntimeError(f'Refusing to replace PASS-pinned source {module}: {expected}')
    live_path = HERE / 'lean_live_status.json'
    if live_path.exists():
        live = json.loads(live_path.read_bytes())
        if live.get('live') and live.get('module') == module and raw != current:
            raise RuntimeError(f'Refusing to replace source marked live: {module}')
    if raw != current:
        path.write_bytes(raw)
