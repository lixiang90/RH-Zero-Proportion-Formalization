"""Freeze Stage A only; producer comparison and mathematical replay stay separate."""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def row(path):
    raw = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest()}


def main():
    out = HERE / "packing-files.json"
    assert not out.exists(), "Preserve frozen manifests"
    replay = json.loads((HERE / "packing-replay.json").read_text(encoding="utf-8"))
    assert row(ROOT / replay["source"]["path"]) == replay["source"]
    files = [row(HERE / name) for name in ["decode_packing.py", "NOTE.zh.md",
        "packing-replay.json", "freeze_package.py"]]
    out.write_text(json.dumps({
        "schema": "independent-new-record-packing-stage-A-package-v1",
        "package_files": files, "dependency_files": [replay["source"]],
        "scope": "137 ordinary Nat payloads and declaration metadata only",
        "producer_imports": 0, "walk_or_leaf_math_replay": False,
        "actual_kernel_evaluations": 0, "Lean_invocations": 0,
        "new_floor_proven": False, "website_submission_ready": False},
        ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(row(out), ensure_ascii=False))


if __name__ == "__main__":
    main()
