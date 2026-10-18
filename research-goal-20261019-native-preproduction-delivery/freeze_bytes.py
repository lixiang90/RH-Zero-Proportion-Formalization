"""One write-new, byte-only archival pass. No research or verifier imports."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(__file__).resolve().parent
ARCHIVE = ROOT / "research-goal-20261019-native-tools-result"
CHUNK = 3 * 1024 * 1024
MANIFESTS = {
    "research-goal-20261019-native-tools-preparation-v2/prepared-files.json": "b7fd183217077da32688e8c23b399ac9f25713e79b107a13466b57fcf33caac2",
    "research-goal-20261019-tiny-production-preparation-v2/prepared-files.json": "f2ab9d281bf39769da08280f40d9369e9b9ffc2f51c57acccbb116999daa9d74",
    "research-goal-20261019-tiny-production-v2-static-review/files.json": "b8e863226254bcd96d4e9c7414c0557e6ae0d92390397a7868315f561f333122",
}
EXTRAS = {
    "research-goal-20261016/gates/tiny-native-trusted-setup-v2-20261019.json": "484120ef295bbf26c438abdf1e15832020b09a2a7bd25b90d6a4c842916a1c87",
    "research-goal-20261016/gates/tiny-native-production-cold-v2-20261019.json": "3cd2bc378f815b53d5c31233d89662c090b04bcdabc489c115f3a4d66924631a",
}
INSTALL = "tmp/current-s1r-tiny-20261018/native-tools-v2/installation.json"
INSTALL_SHA = "2b636d4a943acfdd44bc14225c3128992c2df634320a6623f735b362e220e797"
FAILURE = "research-goal-20261019-native-tools-preparation-v2/v1-failure.json"
FAILURE_SHA = "554d3e54b832dc6d664daf335a0114734a14743ead794de374dbe9d58577e77a"
FRESH = "tmp/goal-20261016/macro006-native-preproduction-fresh-record.json"
FRESH_SHA = "f03c572c86a9dd195eeb3742c570c4462b865c1c081b8112552469c7b3eb3510"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def row(path):
    b = (ROOT / path).read_bytes()
    return {"path": path, "bytes": len(b), "sha256": digest(b)}


def write_new(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as f:
        f.write(data)


def write_json(path, value):
    write_new(path, (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf8"))


def archive_large(source, expected, name, destination):
    b = (ROOT / source).read_bytes()
    assert digest(b) == expected, source
    parts = []
    for i, start in enumerate(range(0, len(b), CHUNK)):
        path = ARCHIVE / "pieces" / (name + f".part{i:02d}")
        write_new(path, b[start:start + CHUNK])
        parts.append(row(path.relative_to(ROOT).as_posix()))
    joined = b"".join((ROOT / x["path"]).read_bytes() for x in parts)
    assert joined == b, source
    return {"source_path": source, "restore_path": destination,
            "bytes": len(b), "sha256": expected, "pieces": parts,
            "split_join_byte_identity_verified": True}


def main():
    candidates = set(MANIFESTS) | set(EXTRAS)
    checked, checks, excluded, external = {}, [], {}, []
    for manifest, expected in MANIFESTS.items():
        assert row(manifest)["sha256"] == expected, manifest
        obj = json.loads((ROOT / manifest).read_text("utf8"))
        counts = {}
        for field in ("files", "dependencies", "read_dependencies"):
            rs = obj.get(field, [])
            counts[field] = len(rs)
            for r in rs:
                path = r["path"]
                if path not in checked:
                    checked[path] = row(path)
                assert checked[path]["bytes"] == r["bytes"], (manifest, path, "bytes")
                assert checked[path]["sha256"] == r["sha256"], (manifest, path, "sha256")
                candidates.add(path)
        external.extend({**x, "manifest": manifest,
                         "verification": "external SDK identity only, not reread or delivered"}
                        for x in obj.get("external_read_dependencies_not_for_Git", []))
        checks.append({**row(manifest), "pin_rows_verified": counts})
    for path, expected in EXTRAS.items():
        assert row(path)["sha256"] == expected, path
    # Only these frozen preparation directories, never the running proof job/draft.
    unpinned = []
    for directory in sorted({str(Path(m).parent).replace("\\", "/") for m in MANIFESTS}):
        for p in sorted((ROOT / directory).rglob("*")):
            if p.is_file():
                path = p.relative_to(ROOT).as_posix()
                assert not any(t in p.name.lower() for t in (".tmp", ".partial", ".lock")), path
                if path not in candidates:
                    unpinned.append(path)
                candidates.add(path)
    assert not unpinned, unpinned
    install = json.loads((ROOT / INSTALL).read_text("utf8"))
    assert install["passed"] is True and install["proof_runs"] == 0
    assert install["official_website_acceptance"] is False
    assert install["gate_sha256"] == EXTRAS["research-goal-20261016/gates/tiny-native-trusted-setup-v2-20261019.json"]
    assert install["prepared_sha256"] == MANIFESTS["research-goal-20261019-native-tools-preparation-v2/prepared-files.json"]
    logical = [
        archive_large(INSTALL, INSTALL_SHA, "installation.json",
                      "research-goal-20261019-native-tools-result/installation.json"),
        archive_large(FAILURE, FAILURE_SHA, "v1-failure.json", FAILURE),
    ]
    fb = (ROOT / FRESH).read_bytes()
    assert digest(fb) == FRESH_SHA
    write_new(ARCHIVE / "fresh-record.json", fb)
    result = {
        "schema": "trusted-native-setup-result-lossless-byte-archive-v1",
        "scope": "Frozen setup metadata and previous prebuild failure, not a candidate proof result",
        "logical_large_metadata_files": logical,
        "fresh_record_snapshot": {**row((ARCHIVE / "fresh-record.json").relative_to(ROOT).as_posix()),
                                  "original_path": FRESH},
        "setup_receipt_metadata": {
            "passed": True, "proof_runs": 0, "official_website_acceptance": False,
            "user_oleans_compiled_or_reused": install["user_oleans_compiled_or_reused"],
            "elapsed_setup_seconds": install["elapsed_setup_seconds"],
            "all_source_and_SDK_checks_reported_unchanged": install["complete_source_and_SDK_C_toolchain_unchanged"],
        },
        "receipt_artifact_pins_are_metadata_only": True,
        "ELF_SDK_C_olean_files_copied": False,
        "producer_or_proof_execution_by_archiver": False,
    }
    write_json(ARCHIVE / "archive.json", result)
    included = []
    forbidden = (".olean", ".ilean", ".ndjson", ".jsonl", ".gz", ".zst", ".zip", ".bin", ".exe", ".dll", ".pyd", ".so", ".a")
    for path in sorted(candidates):
        if path == FAILURE:
            excluded[path] = {"path": path, "reason": "large JSON preserved losslessly by listed pieces and combined SHA"}
        elif path.startswith("tmp/") or path.lower().endswith(forbidden):
            excluded[path] = {"path": path, "reason": "temporary/runtime/archive retained by internal pin, not copied into delivery"}
        else:
            p = ROOT / path
            assert p.stat().st_size <= 4 * 1024 * 1024, path
            p.read_bytes().decode("utf8")
            included.append(row(path))
    for p in sorted(ARCHIVE.rglob("*")):
        if p.is_file():
            included.append(row(p.relative_to(ROOT).as_posix()))
    verification = {
        "schema": "native-preproduction-delivery-byte-audit-v1",
        "internal_manifests": checks,
        "pin_rows_verified": sum(sum(x["pin_rows_verified"].values()) for x in checks),
        "unique_internal_pin_files_verified": len(checked),
        "all_internal_pins_match": True,
        "directory_partial_files_found": [],
        "external_runtime_metadata": external,
        "archive_combined_hashes_and_split_join_verified": True,
        "network_compiler_math_producer_runs": 0,
        "old_frozen_files_modified": False,
    }
    write_json(OUT / "verification.json", verification)
    for name in ("freeze_bytes.py", "verification.json", "NOTE.zh.md"):
        included.append(row((OUT / name).relative_to(ROOT).as_posix()))
    included.sort(key=lambda x: x["path"])
    assert len({x["path"] for x in included}) == len(included)
    wrapper = {
        "schema": "native-preproduction-flat-delivery-v1",
        "files": included,
        "runtime_metadata_excluded": list(excluded.values()),
        "external_runtime_metadata_excluded": external,
        "logical_large_metadata_restoration": logical,
        "all_internal_pins_match": True,
        "total_file_bytes": sum(x["bytes"] for x in included),
        "trusted_native_setup_passed_as_recorded": True,
        "setup_candidate_proof_runs": 0,
        "production_v2_preparation_is_not_a_proof_pass": True,
        "live_session84529_or_v4_draft_included": False,
        "full_cold3200s_passed": False,
        "official_website_acceptance": False,
    }
    write_json(OUT / "files.json", wrapper)
    print(json.dumps({"manifest": row((OUT / "files.json").relative_to(ROOT).as_posix()),
                      "file_count": len(included), "file_bytes": wrapper["total_file_bytes"],
                      "pin_rows_verified": verification["pin_rows_verified"],
                      "archive_manifest": row((ARCHIVE / "archive.json").relative_to(ROOT).as_posix())}))


if __name__ == "__main__":
    main()
