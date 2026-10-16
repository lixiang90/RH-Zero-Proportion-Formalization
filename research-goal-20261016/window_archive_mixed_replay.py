"""Freeze a successful partial mixed replay without copying its large export."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent


def sha(path):
    result = hashlib.sha256()
    with path.open("rb") as handle:
        for part in iter(lambda: handle.read(1024 * 1024), b""):
            result.update(part)
    return result.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--destination", default="window-mixed-independent-20261017")
    args = parser.parse_args()
    assert Path(args.destination).name == args.destination
    work = args.work_dir.resolve()
    assert work.is_relative_to(Path("/var/tmp/rh-zero-20261015"))
    receipt_path = work / "verification.json"
    receipt = json.loads(receipt_path.read_text())
    assert receipt["passed"] and receipt["stage"] == "complete"
    assert receipt["inputs_unchanged"] and receipt["default_kernel_passed"]
    assert receipt["independent_nanoda_passed"] and receipt["partial_roots_only"]
    assert not receipt["website_statement_verified"] and not receipt["submission_ready"]
    assert all(sha(Path(path)) == digest for path, digest in receipt["bound_input_sha256"].items())
    roots = HERE / "window-mixed-independent-roots.json"
    assert sha(roots) == receipt["root_manifest_sha256"]
    assert sha(work / "export.ndjson") == receipt["export_sha256"]
    assert (work / "export.ndjson").stat().st_size == receipt["export_bytes"]
    source = ROOT / (receipt["module"].replace(".", "/") + ".lean")
    files = {
        "receipt.json": receipt_path,
        "selected-roots.json": roots,
        "selected-roots.lean": source,
        "replay.py": HERE / "window_mixed_independent_replay.py",
        "roots-generator.py": HERE / "window_generate_mixed_independent_roots.py",
        "nanoda-config.json": work / "nanoda-config.json",
    }
    for stage in ("export", "default-kernel", "nanoda"):
        for suffix in (".log", "-resources.log"):
            files[stage + suffix] = work / "logs" / (stage + suffix)
    assert all(path.is_file() for path in files.values())
    destination = HERE / args.destination
    assert not destination.exists(), "Keep prior archives immutable; select a new directory"
    destination.mkdir()
    for name, original in files.items():
        shutil.copyfile(original, destination / name)
    pins = {key: receipt[key] for key in ("pins", "runtime", "tool_provenance", "tool_compilation")}
    (destination / "tools-pins.json").write_text(json.dumps(pins, indent=2) + "\n")
    archived = [{"file": path.name, "bytes": path.stat().st_size, "sha256": sha(path)}
                for path in sorted(destination.iterdir())]
    manifest = {
        "scope": receipt["scope"],
        "selected_roots": receipt["roots"],
        "partial_roots_only": True,
        "ordinary_and_independent_kernel_pass": True,
        "website_statement_verified": False,
        "global_energy_floor_proven": False,
        "unconditional_counting_proven": False,
        "submission_ready": False,
        "export": {"bytes": receipt["export_bytes"], "sha256": receipt["export_sha256"],
                   "archived": False, "retained_local_path": str(work / "export.ndjson")},
        "files": archived,
        "archived_bytes_excluding_manifest": sum(row["bytes"] for row in archived),
        "archive_generator_sha256": sha(Path(__file__)),
        "old_22_root_archive_unchanged": True,
    }
    target = destination / "archive-manifest.json"
    target.write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({"directory": str(destination), "manifest_sha256": sha(target),
                      "files": len(archived) + 1, "large_export_archived": False}))


if __name__ == "__main__":
    main()
