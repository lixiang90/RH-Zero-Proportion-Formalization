"""Freeze a static source-specific direction review; do not include live governance."""
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
    assert not output.exists(), "Preserve frozen manifests"
    receipt = json.loads((HERE / "static-receipt.json").read_text(encoding="utf-8"))
    dependencies = [receipt["source"]] + receipt["existing_bridge_body_cost_references_only"]
    for item in dependencies:
        assert row(ROOT / item["path"]) == item
    files = [row(HERE / name) for name in ["audit_static.py", "NOTE.zh.md",
        "static-receipt.json", "freeze_package.py"]]
    output.write_text(json.dumps({
        "schema": "new-record-overlap-static-direction-review-package-v1",
        "package_files": files, "dependency_files": dependencies,
        "scope": "Fresh s1R13 W9 source only; original separation 17/20; no old literal/premise migration claim",
        "new_optimizer_calls": 0, "new_actual_kernel_evaluations": 0,
        "leaf_or_literal_payloads_decoded": 0, "Lean_invocations": 0,
        "new_global_floor_proven": False, "website_submission_ready": False},
        ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(row(output), ensure_ascii=False))


if __name__ == "__main__":
    main()
