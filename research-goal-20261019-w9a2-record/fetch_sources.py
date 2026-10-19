"""Archive immutable public evidence for the W9A2 record; never overwrite."""
import hashlib
import json
import pathlib
import urllib.request
from datetime import datetime, timezone

ROOT = pathlib.Path(__file__).resolve().parent
COMMIT = "4889ee768b6b4d9d2aedd5de8445adb151768fd8"
PREFIX = f"https://raw.githubusercontent.com/josusanmartin/riemann/{COMMIT}/submissions/ajp88-w9a2-window-nine-point/"

def main():
    records = []
    for path in ["proof/Solution.lean", "submission.json", "verification/attestation.json", "verification/verifier.log"]:
        target = ROOT / "official" / path
        if target.exists():
            raise FileExistsError(target)
        url = PREFIX + path
        with urllib.request.urlopen(url, timeout=60) as response:
            data = response.read()
            headers = dict(response.headers)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        records.append({"path": target.relative_to(ROOT).as_posix(), "url": url, "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest(), "headers": headers})
    receipt = {"retrievedAt": datetime.now(timezone.utc).isoformat(), "sourceCommit": COMMIT, "files": records}
    (ROOT / "source-receipt.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"sourceCommit": COMMIT, "files": [{k: r[k] for k in ["path", "bytes", "sha256"]} for r in records]}, indent=2))

if __name__ == "__main__":
    main()
