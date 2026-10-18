"""Write-new flat wrapper for three frozen verification manifests; byte-only."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(__file__).resolve().parent
MANIFESTS = {
    "research-goal-20261019-official-policy-acceptance-audit/files.json": "c81233bd518171c2955adaa567022336c8f2f53fdae63bd912528bdcb0659179",
    "research-goal-20261019-accepted-materials-independent/audit-files.json": "c7cab3dd4794e06ce608d2d95829f189f9205ec370ebcb89cac4445335186498",
    "submission/single-exception-overlap-accepted-20261019/verification-addendum-files.json": "f5ac1380d26469b59eca9fbd0eb367d3d28d308a99d20cdb49786c2a1fa9b205",
}


def row(path):
    b = (ROOT / path).read_bytes()
    return {"path": path, "bytes": len(b), "sha256": hashlib.sha256(b).hexdigest()}


def write_new(name, obj):
    with (OUT / name).open("x", encoding="utf8", newline="\n") as f:
        json.dump(obj, f, ensure_ascii=False, indent=2)
        f.write("\n")


def main():
    paths, verified, audits = set(MANIFESTS), {}, []
    for manifest, expected in MANIFESTS.items():
        assert row(manifest)["sha256"] == expected, manifest
        obj = json.loads((ROOT / manifest).read_text("utf8"))
        counts = {}
        for field in ("files", "dependencies", "read_dependencies"):
            rs = obj.get(field, [])
            counts[field] = len(rs)
            for r in rs:
                path = r["path"]
                if manifest.startswith("submission/") and field == "files":
                    path = (Path(manifest).parent / path).as_posix()
                if path not in verified:
                    verified[path] = row(path)
                a = verified[path]
                assert a["bytes"] == r["bytes"] and a["sha256"] == r["sha256"], (manifest, path)
                paths.add(path)
        audits.append({**row(manifest), "pin_rows_verified": counts})
    verification = {
        "schema": "final-official-verification-addendum-byte-audit-v1",
        "internal_manifests": audits,
        "pin_rows_verified": sum(sum(x["pin_rows_verified"].values()) for x in audits),
        "unique_internal_pin_files_verified": len(verified),
        "all_internal_pins_match": True,
        "previous_final_delivery_manifest_unchanged": row("research-goal-20261019-final-accepted-delivery/files.json")["sha256"] == "d3a0f4fcc35af837dc722eb60a928375caa8de11f5034ae0b8d11ecdedf57e63",
        "network_compiler_generator_mathematical_runs": 0,
        "old_frozen_files_or_root_mutable_state_changed": False,
    }
    assert verification["previous_final_delivery_manifest_unchanged"]
    write_new("verification.json", verification)
    for name in ("freeze_bytes.py", "verification.json", "NOTE.zh.md"):
        paths.add((OUT / name).relative_to(ROOT).as_posix())
    rows = []
    for path in sorted(paths):
        p = ROOT / path
        assert not path.startswith("tmp/")
        assert path not in {"README.md", "README.zh.md", "status.json", "research-goal-20261016/DIRECTION.zh.md", "research-goal-20261016/direction-state.json"}
        assert p.suffix.lower() not in {".olean", ".ilean", ".ndjson", ".jsonl", ".exe", ".dll", ".so", ".c", ".o", ".zst", ".gz", ".zip", ".bin"}
        assert p.stat().st_size <= 2000000
        p.read_bytes().decode("utf8")
        rows.append(row(path))
    write_new("files.json", {
        "schema": "final-official-verification-addendum-flat-delivery-v1",
        "files": rows,
        "all_three_internal_manifests_verified": True,
        "all_internal_pins_match": True,
        "total_file_bytes": sum(x["bytes"] for x in rows),
        "maximum_file_bytes": max(x["bytes"] for x in rows),
        "official_policy_attestation_and_verifier_log_are_frozen_public_evidence": True,
        "original_final_delivery_d3a0_not_modified": True,
        "root_final_cloud_sync_receipt_not_created_here": True,
    })
    print(json.dumps({"manifest": row((OUT / "files.json").relative_to(ROOT).as_posix()),
                      "files": len(rows), "bytes": sum(x["bytes"] for x in rows),
                      "pin_rows_verified": verification["pin_rows_verified"]}))


if __name__ == "__main__":
    main()
