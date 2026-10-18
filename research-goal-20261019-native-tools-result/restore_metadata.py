"""Verify pieces by default; --restore writes missing exact JSON metadata only."""
from pathlib import Path
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--restore", action="store_true")
    args = ap.parse_args()
    archive = json.loads((Path(__file__).parent / "archive.json").read_text("utf8"))
    checked = []
    for item in archive["logical_large_metadata_files"]:
        parts = []
        for part in item["pieces"]:
            b = (ROOT / part["path"]).read_bytes()
            assert len(b) == part["bytes"] and hashlib.sha256(b).hexdigest() == part["sha256"]
            parts.append(b)
        data = b"".join(parts)
        assert len(data) == item["bytes"] and hashlib.sha256(data).hexdigest() == item["sha256"]
        dest = (ROOT / item["restore_path"]).resolve()
        assert dest.is_relative_to(ROOT)
        if dest.exists():
            assert dest.read_bytes() == data, str(dest)
        elif args.restore:
            dest.parent.mkdir(parents=True, exist_ok=True)
            with dest.open("xb") as f:
                f.write(data)
        checked.append({"path": item["restore_path"], "sha256": item["sha256"]})
    print(json.dumps({"all_piece_and_combined_hashes_match": True,
                      "restore_requested": args.restore, "logical_files": checked}))


if __name__ == "__main__":
    main()
