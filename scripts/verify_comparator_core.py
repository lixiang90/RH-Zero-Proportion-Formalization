"""Audit existing compiled exports with the pinned Comparator core.

This is a local statement/axiom/default-kernel audit. It does not run the
website Linux sandbox, invoke nanoda, or submit a result.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
TOOLCHAIN = "+leanprover/lean4:v4.33.0-rc2"
COMPARATOR = "273294467ce06429e6667ece7f5699f8678c9f4e"
EXPORTER = "b18d673bd29b476466a51a3be1012df2ed322b10"
ALLOWED = ["propext", "Quot.sound", "Classical.choice"]
BUILTINS = ["Nat", "String", "String.mk", "Char", "Quot", "Quot.mk", "Quot.lift", "Quot.ind"]
PRIMITIVES = ["Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce"]


def sha(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def capture(command: list[str], cwd: Path = ROOT) -> str:
    proc = subprocess.run(command, cwd=cwd, capture_output=True, text=True, encoding="utf-8", errors="replace")
    if proc.returncode:
        raise RuntimeError(f"Command exited {proc.returncode}: {command}\n{proc.stderr}")
    return proc.stdout.strip()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solution-module", required=True)
    parser.add_argument("--challenge-module", default="Challenge.Candidate")
    parser.add_argument("--solution-root", type=Path, default=Path("tmp/verification"))
    parser.add_argument("--challenge-root", type=Path, default=Path("tmp/contract"))
    parser.add_argument("--comparator-checkout", type=Path, default=Path("tmp/Comparator"))
    parser.add_argument("--exporter-checkout", type=Path, default=Path("tmp/lean4export"))
    parser.add_argument("--target", action="append", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--scope", required=True)
    args = parser.parse_args()
    for name in [args.solution_module, args.challenge_module, *args.target]:
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", name):
            parser.error("Expected ordinary Lean identifiers")
    paths = {key: (ROOT/getattr(args, key)).resolve() for key in ["solution_root", "challenge_root", "comparator_checkout", "exporter_checkout", "output"]}
    if any(not path.is_relative_to(ROOT) for path in paths.values()) or not paths["output"].is_relative_to(ROOT/"verification"):
        parser.error("Inputs must be in this repository; records must be in verification/")
    lake, lean, git = (shutil.which(name) for name in ["lake", "lean", "git"])
    if not all([lake, lean, git]):
        parser.error("Lake, Lean and Git must be on PATH")
    version = capture([lean, TOOLCHAIN, "--version"])
    if "version 4.33.0-rc2" not in version:
        parser.error("Pinned Lean 4.33.0-rc2 required")
    for key, pin in [("comparator_checkout", COMPARATOR), ("exporter_checkout", EXPORTER)]:
        if capture([git, "rev-parse", "HEAD"], paths[key]) != pin:
            parser.error("Incorrect checkout pin: " + key)
        if capture([git, "diff", "--name-only", "HEAD", "--", "*.lean", "lake-manifest.json", "lakefile.toml"], paths[key]):
            parser.error("Pinned tool source has tracked edits: " + key)
    comparator = paths["comparator_checkout"]
    manifest = json.loads((comparator/"lake-manifest.json").read_text(encoding="utf-8"))
    if not any(item.get("name") == "lean4export" and item.get("rev") == EXPORTER for item in manifest["packages"]):
        parser.error("Comparator manifest must bind the pinned exporter")
    capture([lake, TOOLCHAIN, "--no-cache", "build", "comparator"], comparator)
    parser_package = comparator/".lake/packages/lean4export"
    if capture([git, "rev-parse", "HEAD"], parser_package) != EXPORTER:
        parser.error("Comparator parser package must use the pinned exporter")
    if capture([git, "diff", "--name-only", "HEAD", "--", "*.lean"], parser_package):
        parser.error("Comparator parser source has tracked edits")
    exporter = paths["exporter_checkout"]/".lake/build/bin"/("lean4export.exe" if os.name == "nt" else "lean4export")
    driver = ROOT/"tools/ComparatorCoreAudit.lean"
    folder = ROOT/"tmp/comparator-core"
    folder.mkdir(parents=True, exist_ok=True)
    stem = re.sub(r"[^A-Za-z_0-9]", "_", paths["output"].stem)
    def runtime(cwd: Path) -> dict[str, str]:
        data = json.loads(capture([lake, TOOLCHAIN, "--no-cache", "env", sys.executable, "-c", 'import os,json; print(json.dumps({"PATH":os.environ["PATH"],"LEAN_PATH":os.environ.get("LEAN_PATH","")}))'], cwd))
        return {**os.environ, **data}
    export_env = runtime(ROOT)
    export_env["LEAN_PATH"] = os.pathsep.join([str(paths["challenge_root"]), str(paths["solution_root"]), export_env["LEAN_PATH"]])
    core_env = runtime(comparator)
    snapshots = {driver: sha(driver), Path(__file__).resolve(): sha(Path(__file__).resolve()), exporter: sha(exporter)}
    for key, module in [("challenge_root", args.challenge_module), ("solution_root", args.solution_module)]:
        olean = paths[key].joinpath(*module.split(".")).with_suffix(".olean")
        if not olean.is_file():
            parser.error("Compile module before auditing: " + str(olean))
        snapshots[olean] = sha(olean)
        source = olean.with_suffix(".lean")
        if source.is_file():
            snapshots[source] = sha(source)
    for path in paths["challenge_root"].rglob("*.lean"):
        snapshots[path] = sha(path)
    for path in paths["challenge_root"].rglob("*.olean"):
        snapshots[path] = sha(path)
    for path in comparator.rglob("*.lean"):
        if ".lake" not in path.relative_to(comparator).parts:
            snapshots[path] = sha(path)
    snapshots[comparator/"lake-manifest.json"] = sha(comparator/"lake-manifest.json")
    for path in (comparator/".lake/build/lib/lean").rglob("*.olean"):
        snapshots[path] = sha(path)
    for path in (parser_package/".lake/build/lib/lean").rglob("*.olean"):
        snapshots[path] = sha(path)
    for path in parser_package.rglob("*.lean"):
        if ".lake" not in path.relative_to(parser_package).parts:
            snapshots[path] = sha(path)
    roots = list(dict.fromkeys([*BUILTINS, *args.target, *ALLOWED, *PRIMITIVES]))
    start = time.monotonic()
    exports = []
    for label, module in [("challenge", args.challenge_module), ("solution", args.solution_module)]:
        path = folder/(stem + "_" + label + ".ndjson")
        log = folder/(stem + "_" + label + "_export.log")
        command = [str(exporter), module, "--", *roots]
        with path.open("wb") as stdout, log.open("wb") as stderr:
            proc = subprocess.run(command, cwd=ROOT, env=export_env, stdout=stdout, stderr=stderr)
        exports.append({"module": module, "path": path.relative_to(ROOT).as_posix(), "sha256": sha(path), "bytes": path.stat().st_size, "exit_code": proc.returncode, "command": command})
        snapshots[path] = sha(path)
    command = [lean, TOOLCHAIN, "--root="+str(ROOT), "--run", str(driver), str(ROOT/exports[0]["path"]), str(ROOT/exports[1]["path"]), *args.target]
    actual = None
    log = folder/(stem + "_core.log")
    if all(item["exit_code"] == 0 for item in exports):
        with log.open("w", encoding="utf-8", newline="\n") as stream:
            actual = subprocess.run(command, cwd=ROOT, env=core_env, stdout=stream, stderr=subprocess.STDOUT)
    unchanged = all(sha(path) == expected for path, expected in snapshots.items())
    passed = actual is not None and actual.returncode == 0 and unchanged
    record = {"compiler": version, "comparator_commit": COMPARATOR, "exporter_commit": EXPORTER, "theorem_targets": args.target, "export_targets": roots, "input_sha256": {path.relative_to(ROOT).as_posix(): value for path, value in snapshots.items()}, "source_unchanged_during_check": unchanged, "exports": exports, "command": command, "exit_code": actual.returncode if actual else None, "log": log.relative_to(ROOT).as_posix(), "elapsed_seconds": round(time.monotonic()-start, 3), "local_comparator_core_passed": passed, "scope": args.scope, "official_comparator_passed": False, "independent_nanoda_passed": False, "whole_submission_verified": False, "submitted": False}
    paths["output"].write_text(json.dumps(record, indent=2)+"\n", encoding="utf-8", newline="\n")
    print(json.dumps({key: record[key] for key in ["local_comparator_core_passed", "exit_code", "source_unchanged_during_check", "elapsed_seconds", "scope"]}, indent=2), flush=True)
    raise SystemExit(0 if passed else 1)


if __name__ == "__main__":
    main()
