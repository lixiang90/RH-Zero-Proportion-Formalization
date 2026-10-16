"""Read-only hash verification of the frozen four-root replay and sync list."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def main():
    listing = HERE / "window_mixed_independent_sync_files.json"
    assert sha(listing) == "3c3e9bc537d9966df50b6a5a963b9f31b90c2484b5a97ebdeee2ef7a172bb98d"
    paths = json.loads(listing.read_text())
    assert len(paths) == len(set(paths)) == 21
    entries = []
    for relative in paths:
        path = (ROOT / relative).resolve()
        assert path.is_relative_to(ROOT) and path.is_file()
        entries.append({"path": relative, "sha256": sha(path), "bytes": path.stat().st_size})
    archive = HERE / "window-mixed-independent-20261017"
    manifest = archive / "archive-manifest.json"
    assert sha(manifest) == "d14a0180df8860286b774ac86b2589ce860f86ae5fc009c9206c46dba67a7dc6"
    doc = json.loads(manifest.read_text())
    for row in doc["files"]:
        path = archive / row["file"]
        assert sha(path) == row["sha256"] and path.stat().st_size == row["bytes"]
    pairs = {
        "receipt.json": HERE / "window-mixed-independent-replay.json",
        "selected-roots.json": HERE / "window-mixed-independent-roots.json",
        "selected-roots.lean": ROOT / "StructuralGoal20261016/WindowMixedIndependentRoots.lean",
        "replay.py": HERE / "window_mixed_independent_replay.py",
        "roots-generator.py": HERE / "window_generate_mixed_independent_roots.py",
    }
    assert all(sha(archive / name) == sha(path) for name, path in pairs.items())
    assert sha(HERE / "window_archive_mixed_replay.py") == doc["archive_generator_sha256"]
    receipt = json.loads((archive / "receipt.json").read_text())
    assert receipt["passed"] and receipt["independent_nanoda_passed"] and receipt["default_kernel_passed"]
    assert len(receipt["roots"]) == 4 and len(receipt["bound_local_modules"]) == 320
    assert len(receipt["bound_input_sha256"]) == 992
    assert not receipt["global_energy_floor_proven"] and not receipt["submission_ready"]
    assert receipt["partial_roots_only"] and not receipt["website_statement_verified"]
    for path, digest in receipt["bound_input_sha256"].items():
        assert sha(Path(path)) == digest, path
    old_archive = HERE / "window-independent-20261017"
    old = old_archive / "archive-manifest.json"
    assert sha(old) == "684b02c2bd1355cd89f1941f88b1d3c0c0494714df0ab1480b0b027deab87154"
    for name, row in json.loads(old.read_text())["files"].items():
        assert sha(old_archive / name) == row["sha256"]
    out = {"scope": "Read-only check of four selected roots and their 320-module dependency closure, not all roots of those modules.",
           "passed": True, "archive_manifest_sha256": sha(manifest),
           "sync_paths_checked": len(entries), "bound_inputs_rehashed": 992,
           "bound_local_modules": 320, "selected_roots": 4,
           "old_22_root_archive_unchanged": True, "global_energy_floor_proven": False,
           "files": entries, "script_sha256": sha(Path(__file__))}
    (HERE / "window-mixed-archive-hash-recheck.json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({key: value for key, value in out.items() if key != "files"}))


if __name__ == "__main__":
    main()
