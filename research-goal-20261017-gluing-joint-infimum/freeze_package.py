"""Freeze only this static audit and explicitly pinned existing dependencies."""
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
    output = HERE / "joint-infimum-files.json"
    assert not output.exists(), "Preserve the frozen manifest"
    replay = json.loads((HERE / "exact-replay.json").read_text(encoding="utf-8"))
    files = [row(HERE / name) for name in
             ["audit.py", "NOTE.zh.md", "exact-replay.json", "freeze_package.py"]]
    dependencies = replay["source_files"]
    for item in dependencies:
        assert row(ROOT / item["path"]) == item
    packet = {"schema": "saved-support-joint-infimum-static-package-v1",
              "package_files": files, "dependency_files": dependencies,
              "scope": "Only exact saved positive support {0,1}; not all glued ledgers",
              "new_optimizer_calls": 0, "new_actual_kernel_evaluations": 0,
              "Lean_invocations": 0, "new_global_floor_Lean_proven": False,
              "new_unconditional_zero_proportion_proven": False,
              "website_submission_ready": False}
    output.write_text(json.dumps(packet, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(row(output), ensure_ascii=False))


if __name__ == "__main__":
    main()
