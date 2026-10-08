"""Check selected compiled Lean roots with the fixed exporter and WSL Nano.

This is an independent kernel audit, not official Comparator verification.
It never relaxes the three-axiom policy or skips exported unpermitted axioms.
A reused export requires metadata binding its roots, binary, olean and SHA256;
no export process is claimed to have run in that invocation.
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
EXPORTER_PIN = "b18d673bd29b476466a51a3be1012df2ed322b10"
NANODA_PIN = "418320295890faed83a96fd97907b12a3b6728c2"
COMPARATOR_PIN = "273294467ce06429e6667ece7f5699f8678c9f4e"
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
BUILTINS = ["Nat", "String", "String.mk", "Char", "Quot", "Quot.mk", "Quot.lift", "Quot.ind"]
PRIMITIVES = ["Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div",
              "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor",
              "Nat.shiftLeft", "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce"]
IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z_0-9-]*(?:\.[A-Za-z_][A-Za-z_0-9-]*)*")


def digest(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def resolve(path: Path) -> Path:
    return (ROOT / path).resolve()


def git_pin(path: Path, expected: str) -> str:
    actual = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"],
                                     text=True, encoding="utf-8").strip()
    if actual != expected:
        raise ValueError(f"Fixed verifier pin mismatch: {path}: {actual}")
    if subprocess.run(["git", "-C", str(path), "diff", "--quiet", "HEAD", "--"]).returncode:
        raise ValueError(f"Tracked verifier source has local changes: {path}")
    return actual


def snapshot(paths: dict[str, Path]) -> dict[str, str]:
    return {name: digest(path) for name, path in paths.items()}


def lean_name_literal(name: str) -> str:
    """Quote validated module segments for the fixed exporter's name parser."""
    if not IDENTIFIER.fullmatch(name):
        raise ValueError("Expected validated Lean name")
    return ".".join("«" + part + "»" if "-" in part else part
                    for part in name.split("."))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("module")
    parser.add_argument("--root", action="append", required=True)
    parser.add_argument("--include-website-targets", action="store_true",
                        help="Also export the official builtins, three legal axioms and 18 primitives")
    parser.add_argument("--olean", type=Path, required=True)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--lean-path", action="append", type=Path, required=True,
                        help="Directory containing the compiled module; can be repeated")
    parser.add_argument("--exporter-repo", type=Path, default=Path("tmp/lean4export"))
    parser.add_argument("--exporter-bin", type=Path, default=Path("tmp/lean4export/.lake/build/bin/lean4export.exe"))
    parser.add_argument("--nanoda-repo", type=Path, default=Path("tmp/nanoda"))
    parser.add_argument("--nanoda-bin", type=Path, default=Path("tmp/kernel-tools/nanoda-target/release/nanoda_bin"))
    parser.add_argument("--reuse-export", type=Path)
    parser.add_argument("--reuse-metadata", type=Path)
    parser.add_argument("--distribution", default="Ubuntu")
    parser.add_argument("--threads", type=int, choices=range(1, 5), default=4)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--scope", required=True)
    args = parser.parse_args()
    if os.name != "nt":
        parser.error("This driver uses a Windows exporter and WSL Nano")
    if not all(IDENTIFIER.fullmatch(name) for name in [args.module] + args.root):
        parser.error("Expected ordinary Lean module and declaration identifiers")
    if bool(args.reuse_export) != bool(args.reuse_metadata):
        parser.error("Reusing an export requires its bound metadata")
    output = resolve(args.output)
    if not output.is_relative_to(ROOT / "verification"):
        parser.error("Output must stay in verification/")
    lean, lake, wsl = (shutil.which(name) for name in ("lean", "lake", "wsl.exe"))
    if not all((lean, lake, wsl)):
        parser.error("The fixed Lean, Lake and WSL executables must be available")
    version = subprocess.run([lean, "--version"], cwd=ROOT, capture_output=True,
                             text=True, encoding="utf-8", errors="replace")
    if version.returncode or "version 4.33.0-rc2" not in version.stdout:
        parser.error("The website-pinned Lean 4.33.0-rc2 is required")
    exporter_repo, nano_repo = resolve(args.exporter_repo), resolve(args.nanoda_repo)
    pins = {"lean4export": git_pin(exporter_repo, EXPORTER_PIN),
            "nanoda": git_pin(nano_repo, NANODA_PIN), "official_comparator": COMPARATOR_PIN}
    exporter, nano = resolve(args.exporter_bin), resolve(args.nanoda_bin)
    olean, source = resolve(args.olean), resolve(args.source)
    lean_dirs = [resolve(path) for path in args.lean_path]
    expected_olean = Path(*args.module.split(".")).with_suffix(".olean")
    if not any((path / expected_olean).resolve() == olean for path in lean_dirs):
        parser.error("--olean must be the named module under a --lean-path directory")
    roots = list(dict.fromkeys((BUILTINS if args.include_website_targets else []) + args.root +
                              (AXIOMS + PRIMITIVES if args.include_website_targets else [])))
    scratch = ROOT / "tmp/verification" / output.stem
    scratch.mkdir(parents=True, exist_ok=True)
    export = resolve(args.reuse_export) if args.reuse_export else scratch / "export.ndjson"
    metadata_path = resolve(args.reuse_metadata) if args.reuse_metadata else scratch / "export-metadata.json"
    files = {"driver_source": Path(__file__).resolve(), "source_lean": source, "source_olean": olean,
             "exporter_binary": exporter, "nanoda_binary": nano}
    if args.reuse_export:
        files.update({"export": export, "reuse_metadata": metadata_path})
    before = snapshot(files)
    export_command = [str(exporter), lean_name_literal(args.module), "--"] + [lean_name_literal(name) for name in roots]
    export_log = scratch / "export.log"
    export_exit = None
    prior_export_exit = None
    exporter_lean_path = None
    start = time.monotonic()
    if args.reuse_export:
        metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
        expected = {"module": args.module, "roots": roots, "export_exit_code": 0,
                    "exporter_commit": EXPORTER_PIN, "exporter_sha256": before["exporter_binary"],
                    "source_olean_sha256": before["source_olean"], "source_sha256": before["source_lean"],
                    "export_sha256": before["export"], "export_bytes": export.stat().st_size}
        for name, value in expected.items():
            if metadata.get(name) != value:
                parser.error(f"Reused export metadata does not bind {name}")
        prior_export_exit = metadata["export_exit_code"]
    else:
        env_query = subprocess.run([lake, "--no-cache", "env", sys.executable, "-c",
                                   "import os,json;print(json.dumps(dict(os.environ)))"],
                                  cwd=ROOT, capture_output=True, text=True, encoding="utf-8")
        if env_query.returncode:
            raise SystemExit("Unable to obtain the pinned Lake runtime environment")
        environment = json.loads(env_query.stdout)
        environment["LEAN_PATH"] = os.pathsep.join([str(path) for path in lean_dirs] +
                                                   [environment.get("LEAN_PATH", "")])
        exporter_lean_path = environment["LEAN_PATH"]
        print(f"Exporting {len(roots)} roots from {args.module}", flush=True)
        with export.open("wb") as out, export_log.open("wb") as err:
            process = subprocess.run(export_command, cwd=ROOT, env=environment, stdout=out, stderr=err)
        export_exit = process.returncode
        metadata = {"module": args.module, "roots": roots, "export_exit_code": export_exit,
                    "exporter_commit": EXPORTER_PIN, "exporter_sha256": before["exporter_binary"],
                    "source_olean_sha256": before["source_olean"], "source_sha256": before["source_lean"],
                    "export_sha256": digest(export), "export_bytes": export.stat().st_size,
                    "actual_export_command": export_command, "compiler": version.stdout.strip()}
        metadata_path.write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8", newline="\n")
        files.update({"export": export, "export_metadata": metadata_path})
        before.update({"export": digest(export), "export_metadata": digest(metadata_path)})
    configuration = {"use_stdin": True, "permitted_axioms": AXIOMS,
                     "unpermitted_axiom_hard_error": True, "nat_extension": True,
                     "string_extension": True, "num_threads": args.threads,
                     "unsafe_permit_all_axioms": False, "print_success_message": True,
                     "print_axioms": True, "pp_to_stdout": True}
    config_path = scratch / "nanoda-config.json"
    config_path.write_text(json.dumps(configuration, indent=2) + "\n", encoding="utf-8", newline="\n")
    files["configuration"] = config_path
    before["configuration"] = digest(config_path)
    log = scratch / "nanoda.log"
    metrics = scratch / "nanoda-time.txt"
    if metrics.exists():
        metrics.unlink()  # This invocation must never attribute a stale resource log to a failed launch.
    def linux_path(path: Path) -> str:
        result = subprocess.run([wsl, "--distribution", args.distribution, "--exec", "wslpath", "-a", str(path)],
                                cwd=ROOT, capture_output=True, text=True, encoding="utf-8")
        if result.returncode:
            raise RuntimeError(f"Cannot map WSL path: {path}")
        return result.stdout.strip()
    nano_command = [wsl, "--distribution", args.distribution, "--exec", "/usr/bin/time", "-v", "-o",
                    linux_path(metrics), linux_path(nano), linux_path(config_path)]
    nano_exit = None
    nano_elapsed = None
    if export_exit in (None, 0):
        print(f"Nano: {args.threads} threads; {export.stat().st_size} export bytes; {len(roots)} roots", flush=True)
        nano_start = time.monotonic()
        with export.open("rb") as inp, log.open("wb") as out:
            process = subprocess.run(nano_command, cwd=ROOT, stdin=inp, stdout=out, stderr=subprocess.STDOUT)
        nano_exit = process.returncode
        nano_elapsed = round(time.monotonic() - nano_start, 3)
    else:
        log.write_text("Nano not run because the real exporter exited nonzero.\n", encoding="utf-8")
    text = log.read_text(encoding="utf-8", errors="replace")
    count = re.search(r"Checked (\d+) declarations with no errors", text)
    observed = [name.split(".{")[0] for name in re.findall(r"^axiom ([^\s]+)", text, re.MULTILINE)]
    after = snapshot(files)
    unchanged = before == after
    passed = (export_exit in (None, 0) and nano_exit == 0 and count is not None and unchanged
              and set(observed) <= set(AXIOMS))
    record = {"scope": args.scope, "module": args.module, "roots": roots, "compiler": version.stdout.strip(),
              "pins": pins, "input_paths": {name: str(path) for name, path in files.items()},
              "lean_path_directories": [str(path) for path in lean_dirs],
              "exporter_environment_lean_path": exporter_lean_path, "working_directory": str(ROOT),
              "sha256_before": before, "sha256_after": after, "inputs_unchanged": unchanged,
              "existing_compiled_module": True, "module_recompiled_in_this_invocation": False,
              "reused_export": bool(args.reuse_export), "export_process_ran": not bool(args.reuse_export),
              "export_command": export_command, "export_exit_code": export_exit, "prior_export_exit_code": prior_export_exit,
              "prior_export_command": metadata.get("actual_export_command") if args.reuse_export else None,
              "export_bytes": export.stat().st_size, "configuration": configuration,
              "configuration_basis": "Pinned Comparator.Main.runNanoda; only thread scheduling and success/axiom output are added",
              "actual_nano_command": nano_command, "actual_nano_exit_code": nano_exit,
              "nano_elapsed_seconds": nano_elapsed, "total_elapsed_seconds": round(time.monotonic() - start, 3),
              "checked_declarations": int(count.group(1)) if count else None, "observed_axioms": observed,
              "nano_check_passed": passed, "log": str(log.relative_to(ROOT)), "log_sha256": digest(log),
              "resource_log": str(metrics.relative_to(ROOT)),
              "resources": metrics.read_text(encoding="utf-8", errors="replace") if metrics.exists() else None,
              "official_comparator_verified": False, "whole_submission_compiled": False, "submitted": False}
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({"output": str(output.relative_to(ROOT)), "nano_check_passed": passed,
                      "actual_nano_exit_code": nano_exit, "checked_declarations": record["checked_declarations"],
                      "nano_elapsed_seconds": nano_elapsed, "inputs_unchanged": unchanged}, indent=2), flush=True)
    raise SystemExit(0 if passed else 1)


if __name__ == "__main__":
    main()
