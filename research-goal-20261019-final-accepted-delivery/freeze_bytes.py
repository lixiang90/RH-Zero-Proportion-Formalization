"""Final stable flat allowlist: byte checks only, write-new, no model imports."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(__file__).resolve().parent
MANIFESTS = {
    "research-goal-20261019-record-fresh-independent-1745/files.json": "6da14b8ebeb3877cf21400dd9603f9199340f62248081dd7109aa1bb7e7d6916",
    "research-goal-20261019-record-accepted-independent-1753/accepted-files.json": "c528b3b8a5646fe36d924721c5a61ee3193382764dd98cdfa58932f3b2e4b652",
    "research-goal-20261019-record-accepted-independent-1753/files.json": "71f1ba7aaf1ba70b0edf1526103bdf0f1684a4b9c06fbcde3ac5e8a3edb0ebf2",
    "research-goal-20261019-final-requirements-static/files.json": "7fc5ea1a3b013b33e6d7c252986830de6b374fb6c341bc223553db76719aea25",
    "research-goal-20261019-native-materials-preparation/prepared-files.json": "4c9239ec89cbef146a71c18d44e341eca38bda9592a7c92febd2ce1720fef349",
    "research-goal-20261019-native-materials-static-review/files.json": "6104e1fbc51224fcf7d503681a3f2f5182e7102bd98d126842bd5bc1237bf516",
    "research-goal-20261019-native-v4-superseded/files.json": "741e0325ba42ef89ee89ef9267c415fd77bbed693498c63ed17f8c88a99a2545",
    "research-goal-20261019-accepted-materials-preparation/prepared-files.json": "167398a36aa63acdf870692c39129517da0c63c05bd08a965b0cfe3731792f71",
    "research-goal-20261019-accepted-materials-preparation-v1/prepared-files.json": "f123108475be8ac006bf6f46a2189439ecefa1a819b093d0d3b75e02bd01d35c",
    "submission/single-exception-overlap-accepted-20261019/files.json": "11483f1e7214104d842cab76137a11fd22210c7b00a0013e8279414008bc49fd",
}


def row(path):
    b = (ROOT / path).read_bytes()
    return {"path": path, "bytes": len(b), "sha256": hashlib.sha256(b).hexdigest()}


def write_new(name, obj):
    with (OUT / name).open("x", encoding="utf8", newline="\n") as f:
        json.dump(obj, f, ensure_ascii=False, indent=2)
        f.write("\n")


def resolve(manifest, field, path):
    if manifest.startswith("submission/") and field == "files":
        return (Path(manifest).parent / path).as_posix()
    return path


def main():
    candidates, verified, audits = set(MANIFESTS), {}, []
    for manifest, expected in MANIFESTS.items():
        assert row(manifest)["sha256"] == expected, manifest
        obj = json.loads((ROOT / manifest).read_text("utf8"))
        counts = {}
        for field in ("files", "dependencies", "read_dependencies"):
            rs = obj.get(field, [])
            counts[field] = len(rs)
            for r in rs:
                path = resolve(manifest, field, r["path"])
                if path not in verified:
                    verified[path] = row(path)
                a = verified[path]
                assert a["bytes"] == r["bytes"] and a["sha256"] == r["sha256"], (manifest, field, path)
                candidates.add(path)
        audits.append({**row(manifest), "pin_rows_verified": counts})
    # Check all files in the explicitly ready directories, without touching root mutable state.
    dirs = sorted({Path(m).parent.as_posix() for m in MANIFESTS})
    unpinned = []
    for directory in dirs:
        for p in sorted((ROOT / directory).rglob("*")):
            if not p.is_file():
                continue
            path = p.relative_to(ROOT).as_posix()
            assert not any(x in p.name.lower() for x in (".tmp", ".partial", ".lock")), path
            if path not in candidates:
                unpinned.append(path)
            candidates.add(path)
    assert not unpinned, unpinned
    excluded, included = [], []
    forbidden = (".olean", ".ilean", ".ndjson", ".jsonl", ".gz", ".zst", ".zip", ".bin", ".exe", ".dll", ".pyd", ".so", ".a")
    mutable = {"README.md", "README.zh.md", "status.json", "research-goal-20261016/DIRECTION.zh.md", "research-goal-20261016/direction-state.json"}
    for path in sorted(candidates):
        if path.startswith("tmp/") or path in mutable or path.lower().endswith(forbidden):
            excluded.append({"path": path, "reason": "runtime/temporary original or root mutable state retained by pin only"})
            continue
        p = ROOT / path
        assert p.stat().st_size <= 2000000, path
        p.read_bytes().decode("utf8")
        included.append(row(path))
    verification = {
        "schema": "final-accepted-delivery-byte-audit-v1",
        "scope": "Only file byte/size/hash and ready-directory inventory; no network, compiler or mathematical evaluation",
        "internal_manifests": audits,
        "internal_pin_rows_verified": sum(sum(x["pin_rows_verified"].values()) for x in audits),
        "unique_internal_pin_files_verified": len(verified),
        "all_internal_pins_match": True,
        "temporary_partial_files_found": [],
        "old_frozen_files_and_root_state_modified": False,
        "network_compiler_generator_or_math_runs": 0,
    }
    write_new("verification.json", verification)
    for name in ("freeze_bytes.py", "verification.json", "NOTE.zh.md"):
        included.append(row((OUT / name).relative_to(ROOT).as_posix()))
    included.sort(key=lambda x: x["path"])
    assert len({x["path"] for x in included}) == len(included)
    final = {
        "schema": "final-accepted-proof-flat-delivery-v1",
        "files": included,
        "runtime_metadata_excluded": excluded,
        "all_internal_pins_match": True,
        "internal_manifests_verified": len(audits),
        "total_file_bytes": sum(x["bytes"] for x in included),
        "maximum_file_bytes": max(x["bytes"] for x in included),
        "official_accepted_submission_id": "lixiang90-single-exception-overlap-20261018",
        "official_accepted_source_sha256": "024902a7ef01ccba2a6c71e54682a31712417e5d3c0b4ead5f6f80ad25fd1a81",
        "accepted_manifest_and_source_match_user_upload_digest": "23e3dd765aa27de76938e056f13d3e0f08d849d0e7c39c6f78c62e7640c0a10f",
        "official_v3_acceptance_confirmed_by_bound_public_evidence": True,
        "native_v4_cancelled_after_official_v3_acceptance": True,
        "native_v4_full_PASS_or_mathematical_counterexample_claimed": False,
        "unused_native_materials_packages_remain_preparation_only": True,
        "root_final_cloud_audit_not_created_by_this_wrapper": True,
    }
    write_new("files.json", final)
    print(json.dumps({"manifest": row((OUT / "files.json").relative_to(ROOT).as_posix()),
                      "file_count": len(included), "file_bytes": final["total_file_bytes"],
                      "max_file_bytes": final["maximum_file_bytes"],
                      "internal_manifests_verified": len(audits),
                      "pin_rows_verified": verification["internal_pin_rows_verified"]}))


if __name__ == "__main__":
    main()
