"""Restore byte-exact small compiler receipts/runtime metadata from published mirrors. No Lean/math execution."""
from pathlib import Path
from hashlib import sha256
import json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
m=json.loads((HERE/"files.json").read_bytes())
for row in m["restoration_mapping"]:
    src=(ROOT/row["mirror"]).resolve(); dst=(ROOT/row["original"]).resolve()
    assert src.is_relative_to(ROOT) and dst.is_relative_to(ROOT)
    raw=src.read_bytes(); assert len(raw)==row["bytes"] and sha256(raw).hexdigest()==row["sha256"]
    dst.parent.mkdir(parents=True,exist_ok=True)
    if dst.exists(): assert dst.read_bytes()==raw
    else:
        with dst.open("xb") as f: f.write(raw)
print(json.dumps({"restored_or_verified":len(m["restoration_mapping"]),"mathematical_runs":0}))
