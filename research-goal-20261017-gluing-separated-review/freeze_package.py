"""Freeze static notes and exact coefficient/API replay, without runtime trees."""
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
    output = HERE / "review-files.json"
    assert not output.exists(), "Preserve the frozen manifest"
    receipt = json.loads((HERE / "exact-static.json").read_text(encoding="utf-8"))
    files = [row(HERE / name) for name in ["audit_static.py", "NOTE.zh.md",
        "PREFIX-SUFFIX.zh.md", "exact-static.json", "freeze_package.py"]]
    for item in receipt["source_files"]:
        assert row(ROOT / item["path"]) == item
    output.write_text(json.dumps({
        "schema": "gluing-separated-and-prefix-suffix-static-package-v1",
        "package_files": files, "dependency_files": receipt["source_files"],
        "scope": "Fixed separation is not covered by earlier zero-gap no-go; fixed prefix/suffix opportunity only",
        "new_optimizer_calls": 0, "new_actual_kernel_evaluations": 0,
        "new_leaf_records_decoded": 0, "new_overlap_pair_checks": 0,
        "Lean_invocations": 0, "new_global_floor_Lean_proven": False,
        "new_unconditional_zero_proportion_proven": False,
        "website_submission_ready": False}, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(row(output), ensure_ascii=False))


if __name__ == "__main__":
    main()
