"""Read exact-pin primary C++ source as inert bytes; never load or execute it."""
from pathlib import Path
import hashlib
import json
import os
import urllib.request

HERE = Path(__file__).resolve().parent
PIN = "d8b18978322de05a8f3dba51ef03cf5461676c17"
PATHS = ("src/library/ir_interpreter.cpp", "src/runtime/memory.cpp")

def main():
    rows = []
    for relative in PATHS:
        target = HERE / "primary" / relative
        if target.exists():
            raise RuntimeError("Exclusive output already exists: " + str(target))
        url = f"https://raw.githubusercontent.com/leanprover/lean4/{PIN}/{relative}"
        request = urllib.request.Request(url, headers={"User-Agent": "Codex-static-source-review"})
        with urllib.request.urlopen(request, timeout=40) as response:
            raw = response.read(1024 * 1024 + 1)
            if response.status != 200 or len(raw) > 1024 * 1024:
                raise RuntimeError("Expected small HTTP200 source")
            row = {"URL": url, "effective_URL": response.url, "status": response.status,
                   "path": "primary/" + relative, "bytes": len(raw),
                   "sha256": hashlib.sha256(raw).hexdigest(),
                   "ETag": response.headers.get("ETag"), "Date": response.headers.get("Date")}
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open("xb") as stream:
            stream.write(raw); stream.flush(); os.fsync(stream.fileno())
        rows.append(row)
    with (HERE / "primary-retrieval.json").open("x", encoding="utf-8", newline="\n") as stream:
        json.dump({"scope": "Source-only GET; no source execution, native/API load, Lean or compiler", "Lean_pin": PIN, "files": rows}, stream, indent=2)
        stream.write("\n"); stream.flush(); os.fsync(stream.fileno())
    print(json.dumps(rows))

if __name__ == "__main__":
    main()
