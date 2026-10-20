"""Fetch the two small exact-pin resource-check definitions as inert bytes."""
from pathlib import Path
import hashlib
import json
import os
import urllib.request

here = Path(__file__).resolve().parent
pin = "d8b18978322de05a8f3dba51ef03cf5461676c17"
rows = []
for relative in ("src/runtime/interrupt.h", "src/runtime/interrupt.cpp"):
    target = here / "primary" / relative
    if target.exists():
        raise RuntimeError("Exclusive file exists")
    url = f"https://raw.githubusercontent.com/leanprover/lean4/{pin}/{relative}"
    with urllib.request.urlopen(urllib.request.Request(url, headers={"User-Agent": "Codex-static-source-review"}), timeout=40) as response:
        raw = response.read(1024 * 1024 + 1)
        if response.status != 200 or len(raw) > 1024 * 1024:
            raise RuntimeError("Expected small HTTP200 source")
        row = {"path": "primary/" + relative, "URL": url, "effective_URL": response.url,
               "status": response.status, "bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest(),
               "ETag": response.headers.get("ETag"), "Date": response.headers.get("Date")}
    target.parent.mkdir(parents=True, exist_ok=True)
    with target.open("xb") as stream:
        stream.write(raw); stream.flush(); os.fsync(stream.fileno())
    rows.append(row)
with (here / "interrupt-retrieval.json").open("x", encoding="utf-8", newline="\n") as stream:
    json.dump(rows, stream, indent=2); stream.write("\n"); stream.flush(); os.fsync(stream.fileno())
print(json.dumps(rows))
