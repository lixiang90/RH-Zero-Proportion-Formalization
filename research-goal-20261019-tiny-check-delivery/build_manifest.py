"""Byte-only, write-new sync42 allowlist; never imports a research producer."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(__file__).resolve().parent
MANIFESTS = [
    "research-goal-20261018-tiny-flatten-preparation-v3/prepared-files.json",
    "research-goal-20261018-tiny-production-preparation/prepared-files.json",
    "research-goal-20261019-tiny-kernel-evidence/files.json",
    "research-goal-20261019-nanoda-thread-static-review/files.json",
    "research-goal-20261019-native-verifier-source-audit/files.json",
    "research-goal-20261019-tiny-dedup-static-review/files.json",
    "research-goal-20261019-tiny-dedup-static-review/report-files.json",
    "research-goal-20261019-tiny-dedup-source-preparation/prepared-files.json",
    "research-goal-20261019-tiny-dedup-source-independent/audit-files.json",
    "research-goal-20261019-tiny-flatten-preparation-v4/prepared-files.json",
    "research-goal-20261019-tiny-production-preparation-v1/prepared-files.json",
    "research-goal-20261019-tiny-materials-preparation/prepared-files.json",
    "research-goal-20261019-native-tools-preparation/prepared-files.json",
    "research-goal-20261019-native-tools-preparation-v1/prepared-files.json",
    "submission/single-exception-overlap-20261019/files.json",
]
EXPECTED = {
    "research-goal-20261019-native-tools-preparation/prepared-files.json": "d99de8719d1f42b9f3cd63d9cf71889c24763c08d5256d66502d7ec21d066cbf",
    "research-goal-20261019-native-tools-preparation-v1/prepared-files.json": "a1a7b4659065b19da97c96ba40b7d57312e466f47af31d3f5cc6a12d22efb2b2",
    "submission/single-exception-overlap-20261019/files.json": "2c1fe58da1294dd1847415d519de7ebdfda600f28e9d5f324fd2579fb7515802",
    "research-goal-20261016/gates/tiny-native-trusted-setup-v0-20261019.json": "08c32b1852c790f6f8ff742b39af16d8f9fc63c96e87a035e7abb26da7aaa4bb",
    "research-goal-20261016/gates/tiny-native-trusted-setup-v1-20261019.json": "5c65fe9dfa5ca2f5d5b3bfd095788feb3b4ea21777628283dd404b07c2398689",
}
EXTRAS = [
    "research-goal-20261018-tiny-flatten-preparation-v3/draft/Solution.lean",
    "research-goal-20261018-tiny-flatten-preparation-v3/draft/generation.json",
    "research-goal-20261018-tiny-flatten-preparation-v3/draft/candidate-metadata.json",
    "research-goal-20261019-tiny-nanoda-diagnostic/run_once.py",
    "research-goal-20261016/gates/tiny-production-cold-v0-20261018.json",
    "research-goal-20261016/gates/tiny-native-trusted-setup-v0-20261019.json",
    "research-goal-20261016/gates/tiny-native-trusted-setup-v1-20261019.json",
]


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for part in iter(lambda: f.read(1024 * 1024), b""):
            h.update(part)
    return h.hexdigest()


def row(path):
    p = ROOT / path
    return {"path": path, "bytes": p.stat().st_size, "sha256": sha(p)}


def write_new(name, value):
    with (OUT / name).open("x", encoding="utf8", newline="\n") as f:
        json.dump(value, f, ensure_ascii=False, indent=2)
        f.write("\n")


def main():
    candidates = set(MANIFESTS + EXTRAS)
    checks, excluded, external, checked = [], {}, [], {}
    for manifest in MANIFESTS:
        mp = ROOT / manifest
        if manifest in EXPECTED:
            assert sha(mp) == EXPECTED[manifest], manifest
        obj = json.loads(mp.read_text("utf8"))
        counts = {}
        for field in ("files", "dependencies", "read_dependencies"):
            rows = obj.get(field, [])
            counts[field] = len(rows)
            for r in rows:
                path = r["path"]
                if manifest.startswith("submission/") and field == "files":
                    path = (Path(manifest).parent / path).as_posix()
                p = ROOT / path
                actual = checked.setdefault(path, row(path))
                assert actual["bytes"] == r["bytes"], (manifest, field, path, "bytes")
                assert actual["sha256"] == r["sha256"], (manifest, field, path, "sha256")
                candidates.add(path)
        for r in obj.get("external_read_dependencies_not_for_Git", []):
            external.append({**r, "manifest": manifest,
                             "verification": "excluded external SDK identity; not reread by this byte-only delivery task"})
        ident = obj.get("external_runtime_identity")
        if isinstance(ident, dict) and "path" in ident:
            p = Path(ident["path"])
            assert p.stat().st_size == ident["bytes"] and sha(p) == ident["sha256"], manifest
            external.append({**ident, "manifest": manifest, "verification": "byte identity verified; binary excluded"})
        checks.append({**row(manifest), "pin_rows_verified": counts})
    # Inventory only the explicitly frozen directories. No setup job/output is read.
    dirs = {str(Path(m).parent).replace("\\", "/") for m in MANIFESTS}
    dirs.add("research-goal-20261019-tiny-nanoda-diagnostic")
    unpinned = []
    for directory in sorted(dirs):
        for p in sorted((ROOT / directory).rglob("*")):
            if not p.is_file():
                continue
            path = p.relative_to(ROOT).as_posix()
            assert not any(s in p.name.lower() for s in (".partial", ".tmp", ".lock")), path
            if path not in candidates:
                unpinned.append(path)
            candidates.add(path)
    assert set(unpinned) <= {"research-goal-20261018-tiny-flatten-preparation-v3/draft/candidate-metadata.json",
                             "research-goal-20261019-tiny-nanoda-diagnostic/run_once.py"}, unpinned
    for path, expected in EXPECTED.items():
        assert sha(ROOT / path) == expected, path
    included = []
    forbidden = (".olean", ".ilean", ".ndjson", ".jsonl", ".gz", ".zst", ".zip", ".bin", ".exe", ".dll", ".pyd", ".so", ".a")
    for path in sorted(candidates):
        if path.startswith("tmp/") or path.lower().endswith(forbidden):
            excluded[path] = {"path": path, "reason": "runtime/temporary original or archive retained by internal pin only; frozen evidence copies are separately included"}
            continue
        p = ROOT / path
        assert p.stat().st_size <= 4 * 1024 * 1024, path
        p.read_bytes().decode("utf8")
        included.append(row(path))
    verification = {
        "schema": "tiny-check-delivery-byte-pin-audit-v1",
        "scope": "Hash, size, UTF-8 and frozen-directory inventory only; no producer/model imports or theorem evaluation",
        "internal_manifests": checks,
        "internal_pin_rows_verified": sum(sum(x["pin_rows_verified"].values()) for x in checks),
        "unique_internal_pin_files_verified": len(checked),
        "all_internal_pins_match": True,
        "temporary_partial_files_found": [],
        "newly_fixed_extra_files": EXTRAS,
        "external_identity_metadata": external,
        "runtime_setup_receipts_included": False,
        "compiler_network_math_runs": 0,
        "old_files_modified": False,
    }
    write_new("verification.json", verification)
    for name in ("build_manifest.py", "verification.json", "NOTE.zh.md"):
        included.append(row((OUT / name).relative_to(ROOT).as_posix()))
    included.sort(key=lambda x: x["path"])
    result = {
        "schema": "tiny-check-evidence-flat-delivery-v1",
        "files": included,
        "runtime_metadata_excluded": list(excluded.values()),
        "external_runtime_metadata_excluded": external,
        "internal_manifests_verified": len(checks),
        "all_internal_pins_match": True,
        "total_file_bytes": sum(x["bytes"] for x in included),
        "v3_actual_flattened_source_included": True,
        "v4_generator_executed_by_this_delivery": False,
        "production_v1_and_materials_are_preparation_only": True,
        "native_setup_v0_v1_are_static_preparations_not_success_receipts": True,
        "live_or_later_setup_receipts_included": False,
        "full_cold3200s_passed": False,
        "official_website_acceptance": False,
    }
    write_new("files.json", result)
    print(json.dumps({"manifest": row((OUT / "files.json").relative_to(ROOT).as_posix()),
                      "file_count": len(included), "total_file_bytes": result["total_file_bytes"],
                      "internal_manifests_verified": len(checks),
                      "pin_rows_verified": verification["internal_pin_rows_verified"],
                      "excluded_paths": len(excluded)}, ensure_ascii=False))


if __name__ == "__main__":
    main()
