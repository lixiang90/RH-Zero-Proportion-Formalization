"""Fetch a bounded, commit-pinned public policy snapshot; never run its code."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import urllib.request

HERE = Path(__file__).resolve().parent
REPO = "josusanmartin/riemann"
PATHS = [
    "CONTRIBUTING.md", "SECURITY.md", "challenge/contract.json",
    "scripts/prepare-candidate.ts", "scripts/verify-submission.ts",
    "scripts/run-comparator-e2b.sh", "scripts/run-lake-build-bounded-disk.sh",
    "e2b/run-verification-job.sh", "src/lib/e2b-config.ts",
]


def fetch(url):
    request = urllib.request.Request(url, headers={"User-Agent": "RH-Zero-research-readonly"})
    with urllib.request.urlopen(request, timeout=40) as response:
        raw = response.read(600001)
    assert len(raw) <= 600000
    return raw


def main():
    assert not (HERE / "policy-snapshot.json").exists(), "Preserve existing snapshot"
    meta = json.loads(fetch(f"https://api.github.com/repos/{REPO}/commits/main"))
    commit = meta["sha"]
    assert len(commit) == 40 and all(c in "0123456789abcdef" for c in commit)
    rows = []
    for relative in PATHS:
        url = f"https://raw.githubusercontent.com/{REPO}/{commit}/{relative}"
        raw = fetch(url)
        target = HERE / "snapshot" / relative
        assert not target.exists()
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(raw)
        rows.append({"path": str(target.relative_to(HERE.parent)).replace("\\", "/"),
                     "upstream_path": relative, "url": url,
                     "bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()})
    result = {"schema": "read-only-generator-policy-snapshot-v1",
              "retrieved_UTC": datetime.now(timezone.utc).isoformat(),
              "repository": REPO, "commit": commit, "files": rows,
              "downloaded_code_executed": False, "policy_is_formal_proof": False}
    (HERE / "policy-snapshot.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"commit": commit, "files": len(rows), "bytes": sum(r["bytes"] for r in rows)}))


if __name__ == "__main__":
    main()
