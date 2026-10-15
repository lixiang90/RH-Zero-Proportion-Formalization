"""Verify the uploadable single file in an isolated trusted-package overlay.

Local verification only: no website sandbox, upload, or official acceptance.
All generated files stay in --work-dir, which must be a fresh directory for
compilation. The default runtime uses the pinned read-only WSL package cache.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
WORKSPACE = ROOT.parent
SIBLING = Path("E:/codex-build/RH-Zero-Proportion-Formalization")
TOOLCHAIN = "4.33.0-rc2"
PINS = {"Zeta23": "3635e74826a4c1fcece7d1cd2b6fa75e43a00510",
        "mathlib": "51e6992efd06126df61a496bebf8f49482a4e129",
        "Comparator": "273294467ce06429e6667ece7f5699f8678c9f4e",
        "lean4export": "b18d673bd29b476466a51a3be1012df2ed322b10",
        "nanoda": "418320295890faed83a96fd97907b12a3b6728c2"}
ROOTS = ["candidate_strict_improvement", "candidate_critical_line_bound",
         "candidate_critical_line_bound_cumulative"]
ALLOWED = ["propext", "Quot.sound", "Classical.choice"]
PRIMITIVES = ["Nat", "String", "String.mk", "Char", "Quot", "Quot.mk", "Quot.lift",
              "Quot.ind", *ALLOWED, "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow",
              "Nat.gcd", "Nat.div", "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land",
              "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight", "String.ofList",
              "Char.ofNat", "List", "eagerReduce"]


def sha(path: Path) -> str:
    with path.open("rb") as stream:
        digest = hashlib.sha256()
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
        return digest.hexdigest()


def write_json(path: Path, data: dict) -> None:
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf8", newline="\n")


def linux_path(path: Path) -> str:
    path = path.resolve()
    return "/mnt/" + path.drive[0].lower() + str(path)[2:].replace("\\", "/") if os.name == "nt" else str(path)


def git(repo: Path, *args: str) -> bytes:
    return subprocess.check_output(["git", "--no-optional-locks", "--git-dir=" + str(repo / ".git"), *args])


def command_prefix(args) -> list[str]:
    return ["wsl", "--distribution", args.distribution, "--exec"] if os.name == "nt" else []


def capture(args, command: list[str]) -> str:
    return subprocess.check_output(command_prefix(args) + command, text=True, encoding="utf8").strip()


def trusted_runtime(args) -> tuple[str, list[str], dict]:
    handoff = json.loads(args.runtime_manifest.read_text(encoding="utf8"))
    lean = args.lean or handoff["lean"]
    package_paths = [path for path in handoff["lean_path"].split(":") if "/.lake/packages/" in path]
    if not package_paths or any("/.lake/packages/" not in p for p in package_paths):
        raise ValueError("Only trusted package paths are allowed")
    compiler_sha = capture(args, ["sha256sum", lean]).split()[0]
    assert compiler_sha == handoff["lean_sha256"], "Pinned compiler hash mismatch"
    version = capture(args, [lean, "--version"])
    assert TOOLCHAIN in version, "Pinned compiler version mismatch"
    dependency_manifest = json.loads(args.package_manifest.read_text(encoding="utf8"))
    dependencies = {p["name"]: p["rev"] for p in dependency_manifest["packages"]}
    assert dependencies["mathlib"] == PINS["mathlib"] and dependencies["Zeta23"] == PINS["Zeta23"]
    return lean, package_paths, {"compiler": lean, "compiler_sha256": compiler_sha,
                                 "compiler_version": version, "runtime_manifest_sha256": sha(args.runtime_manifest),
                                 "package_manifest_sha256": sha(args.package_manifest),
                                 "trusted_package_cache_basis": "Existing native package cache named by the archived runtime manifest"}


def pinned_blob(repo: Path, pin: str, name: str) -> bytes:
    assert git(repo, "rev-parse", "HEAD").decode().strip() == pin, (repo, pin)
    return git(repo, "show", "HEAD:" + name)


def lean_command(args, lean: str, paths: list[str], *arguments: str) -> list[str]:
    return command_prefix(args) + ["env", "PATH=" + lean.rsplit("/", 1)[0] + ":/usr/bin:/bin",
                                   "LEAN_PATH=" + ":".join(paths), lean, "-j1", "--tstack=32768",
                                   "-DrelaxedAutoImplicit=false", *arguments]


def compile_one(args, lean: str, paths: list[str], work: Path, module: str) -> dict:
    source = work / "source" / Path(*module.split(".")).with_suffix(".lean")
    output = work / "lib" / Path(*module.split(".")).with_suffix(".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    log = work / "logs" / (module + ".log")
    for prior in [log, log.with_suffix(".json")]:
        if prior.exists():
            attempt = 1
            while prior.with_name(prior.name + f".attempt{attempt}").exists():
                attempt += 1
            prior.rename(prior.with_name(prior.name + f".attempt{attempt}"))
    before = sha(source)
    command = lean_command(args, lean, paths, "-R", linux_path(work / "source"),
                           "-o", linux_path(output), "-i", linux_path(output.with_suffix(".ilean")), linux_path(source))
    started = time.monotonic()
    with log.open("wb") as stream:
        proc = subprocess.run(command, cwd=work, stdout=stream, stderr=subprocess.STDOUT, timeout=args.timeout)
    record = {"module": module, "source": str(source), "source_sha256": before,
              "source_unchanged": before == sha(source), "command": command, "exit_code": proc.returncode,
              "elapsed_seconds": round(time.monotonic() - started, 3), "log": str(log),
              "olean": str(output), "olean_sha256": sha(output) if proc.returncode == 0 else None}
    write_json(work / "logs" / (module + ".json"), record)
    if proc.returncode or not record["source_unchanged"]:
        raise RuntimeError(f"Compilation failed for {module}: {log}")
    print(f"Compiled {module}: {record['elapsed_seconds']} seconds", flush=True)
    return record


def prepare(args, work: Path, runtime: dict) -> dict:
    if work.exists() and any(work.iterdir()):
        raise ValueError("Fresh compilation requires an empty --work-dir")
    for folder in ["source/ChallengeDeps", "source/Challenge", "source/Solution", "logs", "lib"]:
        (work / folder).mkdir(parents=True, exist_ok=True)
    data = args.solution.read_bytes()
    data.decode("utf8")
    solution_sha = hashlib.sha256(data).hexdigest()
    assert sha(args.solution) == solution_sha, "Upload changed while reading"
    assert len(data) <= 2_000_000, "Solution exceeds 2,000,000 UTF-8 bytes"
    site = args.website_repo
    contract = json.loads((site / "challenge/contract.json").read_text(encoding="utf8"))
    assert contract["trustedUpstream"]["commit"] == PINS["Zeta23"]
    assert contract["trustedUpstream"]["mathlibCommit"] == PINS["mathlib"]
    assert contract["verifier"]["comparatorCommit"] == PINS["Comparator"]
    assert contract["verifier"]["lean4exportCommit"] == PINS["lean4export"]
    assert contract["verifier"]["nanodaCommit"] == PINS["nanoda"]
    records = json.loads((site / "data/records.json").read_text(encoding="utf8"))
    current = [r for r in records if r["status"] == "kernel-verified" and r["track"] == "critical-line"][-1]
    assert 0 < Fraction(int(args.numerator), int(args.denominator)) <= 1
    if current["exactRational"]:
        old = Fraction(int(current["exactRational"]["numerator"]), int(current["exactRational"]["denominator"]))
        assert Fraction(int(args.numerator), int(args.denominator)) > old
    site_inputs = {}
    for name in ["challenge/contract.json", "data/records.json", "challenge/templates/CandidateSpec.lean.tmpl",
                 "challenge/templates/Challenge.Candidate.lean"]:
        raw = (site / name).read_bytes()
        assert raw.replace(b"\r\n", b"\n") == git(site, "show", "HEAD:" + name).replace(b"\r\n", b"\n")
        site_inputs[name] = sha(site / name)
    deps = pinned_blob(args.zeta_repo, PINS["Zeta23"], "comparator/ChallengeDeps.lean")
    (work / "source/ChallengeDeps.lean").write_bytes(deps)
    spec = (site / "challenge/templates/CandidateSpec.lean.tmpl").read_text(encoding="utf8")
    spec = spec.replace("{{CURRENT_EXPRESSION}}", current["exactExpression"])
    spec = spec.replace("{{NUMERATOR}}", args.numerator).replace("{{DENOMINATOR}}", args.denominator)
    (work / "source/ChallengeDeps/CandidateSpec.lean").write_text(spec, encoding="utf8", newline="\n")
    (work / "source/Challenge/Candidate.lean").write_text(
        (site / "challenge/templates/Challenge.Candidate.lean").read_text(encoding="utf8"), encoding="utf8", newline="\n")
    (work / "source/Solution/Candidate.lean").write_bytes(data)
    assert sha(work / "source/Solution/Candidate.lean") == solution_sha == sha(args.solution)
    source_hashes = {str(p.relative_to(work)): sha(p) for p in (work / "source").rglob("*.lean")}
    record = {"scope": "Fresh single-file local verification, no website upload", "runtime": runtime,
              "pins": PINS, "solution": str(args.solution), "solution_sha256": solution_sha,
              "solution_bytes": len(data), "current_record": current,
              "score": {"numerator": args.numerator, "denominator": args.denominator},
              "website_source_commit": git(site, "rev-parse", "HEAD").decode().strip(),
              "website_source_sha256": site_inputs, "generated_source_sha256": source_hashes,
              "official_website_acceptance": False, "submitted": False}
    write_json(work / "prepared.json", record)
    return record


def existing_compile(args, work: Path, runtime: dict) -> tuple[dict, list[dict]]:
    """Bind an earlier fresh compile without representing it as a new compile."""
    path = args.reuse_compiled.resolve()
    if path.is_dir():
        compiled = [json.loads((path / "logs" / (module + ".json")).read_text(encoding="utf8"))
                    for module in ["ChallengeDeps", "ChallengeDeps.CandidateSpec", "Solution.Candidate"]]
    else:
        prior = json.loads(path.read_text(encoding="utf8"))
        compiled = prior["compiled_modules"]
    modules = [entry["module"] for entry in compiled]
    assert len(modules) == len(set(modules)), "Reused module receipts are duplicated"
    assert {"ChallengeDeps", "ChallengeDeps.CandidateSpec", "Solution.Candidate"} <= set(modules)
    assert set(modules) <= {"ChallengeDeps", "ChallengeDeps.CandidateSpec", "Solution.Candidate", "Challenge.Candidate"}
    reconstruction = work / "trusted-reconstruction"
    prepared = prepare(args, reconstruction, runtime)
    for entry in compiled:
        assert entry["exit_code"] == 0 and entry["source_unchanged"], entry["module"]
        source = Path(entry["source"])
        if not source.is_absolute():
            source = work / source
        assert source.resolve().is_relative_to(work)
        assert sha(source) == entry["source_sha256"], "Reused compiled source changed"
        expected = reconstruction / "source" / Path(*entry["module"].split(".")).with_suffix(".lean")
        if entry["module"] == "Solution.Candidate":
            assert source.read_bytes() == expected.read_bytes(), "Compiled solution differs from upload"
        else:
            assert source.read_bytes().replace(b"\r\n", b"\n") == expected.read_bytes().replace(b"\r\n", b"\n")
        output = Path(entry.get("olean", work / "lib" / Path(*entry["module"].split(".")).with_suffix(".olean")))
        assert output.resolve().is_relative_to(work)
        expected_output = work / "lib" / Path(*entry["module"].split(".")).with_suffix(".olean")
        assert output.resolve() == expected_output.resolve(), "Reused module has an unexpected output path"
        assert sha(output) == entry.get("olean_sha256", entry.get("output_sha256")), "Reused compiled artifact changed"
        assert any(arg == "LEAN_PATH=" + ":".join([linux_path(work / "lib"), *args.package_paths])
                   for arg in entry["command"]), "Earlier compilation used non-isolated Lean paths"
        assert runtime["compiler"] in entry["command"], "Earlier compilation did not use the pinned compiler"
        if "compiler_sha256" in entry:
            assert entry["compiler_sha256"] == runtime["compiler_sha256"]
        assert linux_path(source) in entry["command"] and linux_path(output) in entry["command"]
        entry.update({"source": str(source.resolve()), "olean": str(output.resolve()), "olean_sha256": sha(output)})
    prepared["compiled_in_prior_invocation"] = True
    prepared["prior_compile_input"] = str(path)
    write_json(work / "prepared-reuse.json", prepared)
    return prepared, compiled


def copy_tools(args, work: Path) -> tuple[Path, dict]:
    tools = work / "tools"
    for folder in ["source", "logs", "lib"]:
        (tools / folder).mkdir(parents=True, exist_ok=True)
    provenance = {}
    for repo, pin, names in [
        (args.exporter_repo, PINS["lean4export"], ["Export.lean", "Export/Parse.lean", "Main.lean"]),
        (args.comparator_repo, PINS["Comparator"], ["Comparator.lean", "Comparator/Axioms.lean",
                                                  "Comparator/Compare.lean", "Comparator/Util.lean", "Main.lean"]),
    ]:
        assert git(repo, "rev-parse", "HEAD").decode().strip() == pin
        for name in names:
            blob = pinned_blob(repo, pin, name)
            output_name = ("ExporterMain.lean" if repo == args.exporter_repo else "ComparatorMain.lean") if name == "Main.lean" else name
            target = tools / "source" / output_name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(blob)
            provenance[str(target.relative_to(work))] = {"git_commit": pin, "git_path": name, "sha256": sha(target)}
    manifest = json.loads(pinned_blob(args.comparator_repo, PINS["Comparator"], "lake-manifest.json"))
    assert any(p["name"] == "lean4export" and p["rev"] == PINS["lean4export"] for p in manifest["packages"])
    assert git(args.nanoda_repo, "rev-parse", "HEAD").decode().strip() == PINS["nanoda"]
    binary_sha = sha(args.nanoda_bin)
    expected_binary = args.nanoda_sha256
    if not expected_binary:
        old = json.loads(args.nanoda_provenance.read_text(encoding="utf8"))
        expected_binary = old["sha256_before"]["nanoda_binary"]
    assert binary_sha == expected_binary, "Nanoda binary differs from its pinned build provenance"
    cargo_blob = pinned_blob(args.nanoda_repo, PINS["nanoda"], "Cargo.toml")
    provenance["nanoda_binary"] = {"path": str(args.nanoda_bin), "sha256": binary_sha, "pin": PINS["nanoda"],
                                   "cargo_git_blob_content_sha256": hashlib.sha256(cargo_blob).hexdigest(),
                                   "provenance_receipt": str(args.nanoda_provenance) if not args.nanoda_sha256 else None}
    driver = ROOT / "tools/ComparatorCoreAudit.lean"
    target = tools / "source/CoreAudit.lean"
    target.write_bytes(driver.read_bytes())
    provenance["core_driver"] = {"path": str(driver), "sha256": sha(driver), "copied_sha256": sha(target)}
    return tools, provenance


def topological_modules(tools: Path) -> list[str]:
    files = [tools / "source/Export.lean", tools / "source/Export/Parse.lean",
             tools / "source/Comparator.lean", *(tools / "source/Comparator").glob("*.lean")]
    sources = {".".join(p.relative_to(tools / "source").with_suffix("").parts): p for p in files}
    pending, order = set(sources), []
    while pending:
        ready = []
        for module in sorted(pending):
            imports = set(re.findall(r"^import\s+(\S+)", sources[module].read_text(encoding="utf8"), re.M))
            if not (imports & pending):
                ready.append(module)
        if not ready:
            raise ValueError("Pinned tool source import cycle")
        order.extend(ready)
        pending.difference_update(ready)
    return order


def run_logged(args, command: list[str], log: Path, *, stdin: Path | None = None,
               binary_output: Path | None = None) -> dict:
    started = time.monotonic()
    inp = stdin.open("rb") if stdin else None
    out = binary_output.open("wb") if binary_output else log.open("wb")
    err = log.open("wb") if binary_output else out
    try:
        proc = subprocess.run(command, stdin=inp, stdout=out, stderr=err, timeout=args.timeout)
    finally:
        if inp:
            inp.close()
        out.close()
        if err is not out:
            err.close()
    record = {"command": command, "exit_code": proc.returncode, "elapsed_seconds": round(time.monotonic() - started, 3),
              "log": str(log), "log_sha256": sha(log)}
    if binary_output:
        record.update({"export": str(binary_output), "export_sha256": sha(binary_output), "export_bytes": binary_output.stat().st_size})
    if proc.returncode:
        raise RuntimeError(f"Verifier stage exited {proc.returncode}: {log}")
    return record


def audit_replay(args, work: Path, lean: str, package_paths: list[str], receipt: dict) -> None:
    paths = [linux_path(work / "lib"), *package_paths]
    assert sha(args.solution) == receipt["solution_sha256"], "Upload changed after compilation"
    for entry in receipt["compiled_modules"]:
        source = Path(entry["source"])
        output = Path(entry["olean"])
        assert sha(source) == entry["source_sha256"] and sha(output) == entry["olean_sha256"]
        if entry["module"] == "Solution.Candidate":
            assert entry["source_sha256"] == receipt["solution_sha256"]
    # Compile the trusted challenge separately; do not rebuild the whole file.
    if not any(r["module"] == "Challenge.Candidate" for r in receipt["compiled_modules"]):
        source = work / "source/Challenge/Candidate.lean"
        source.parent.mkdir(parents=True, exist_ok=True)
        expected = work / "trusted-reconstruction/source/Challenge/Candidate.lean"
        source.write_bytes(expected.read_bytes())
        receipt["compiled_modules"].append(compile_one(args, lean, paths, work, "Challenge.Candidate"))
    tools, provenance = copy_tools(args, work)
    tool_paths = [linux_path(tools / "lib"), *paths]
    receipt["stage"] = "tool-compilation"
    receipt["tool_provenance"] = provenance
    receipt["tool_compiled_modules"] = [compile_one(args, lean, tool_paths, tools, module)
                                        for module in topological_modules(tools)]
    tracked = {str(args.solution): sha(args.solution), str(Path(__file__).resolve()): sha(Path(__file__).resolve()),
               str(args.nanoda_bin): sha(args.nanoda_bin)}
    for name, expected in receipt.get("additional_bound_source_sha256", {}).items():
        assert sha(Path(name)) == expected, "A prepare-bound input changed before replay"
        tracked[name] = expected
    for folder in [work / "source", work / "trusted-reconstruction/source", work / "tools/source"]:
        for path in folder.rglob("*"):
            if path.is_file() and path.suffix == ".lean":
                tracked[str(path)] = sha(path)
    for folder in [work / "lib", work / "tools/lib"]:
        for path in folder.rglob("*"):
            if path.is_file():
                tracked[str(path)] = sha(path)
    for entry in receipt["compiled_modules"]:
        tracked[entry["source"]] = sha(Path(entry["source"]))
        tracked[entry["olean"]] = sha(Path(entry["olean"]))
    for name, expected in receipt["website_source_sha256"].items():
        path = args.website_repo / name
        assert sha(path) == expected
        tracked[str(path)] = expected
    tracked[str(args.runtime_manifest)] = sha(args.runtime_manifest)
    tracked[str(args.package_manifest)] = sha(args.package_manifest)
    if not args.nanoda_sha256:
        tracked[str(args.nanoda_provenance)] = sha(args.nanoda_provenance)
    receipt["sha256_before_replay"] = tracked
    exports = {}
    roots = list(dict.fromkeys([*ROOTS, *PRIMITIVES]))
    for label, module in [("challenge", "Challenge.Candidate"), ("solution", "Solution.Candidate")]:
        receipt["stage"] = label + "-export"
        command = lean_command(args, lean, tool_paths, "--run", linux_path(tools / "source/ExporterMain.lean"), module, "--", *roots)
        exports[label] = run_logged(args, command, work / "logs" / (label + "-export.log"),
                                   binary_output=work / (label + ".ndjson"))
        tracked[str(work / (label + ".ndjson"))] = exports[label]["export_sha256"]
    receipt["exports"] = exports
    receipt["export_roots"] = roots
    receipt["stage"] = "comparator-default-kernel"
    command = lean_command(args, lean, tool_paths, "--run", linux_path(tools / "source/CoreAudit.lean"),
                           linux_path(work / "challenge.ndjson"), linux_path(work / "solution.ndjson"), *ROOTS)
    receipt["comparator_default_kernel"] = run_logged(args, command, work / "logs/comparator-default-kernel.log")
    transcript = (work / "logs/comparator-default-kernel.log").read_text(encoding="utf8", errors="replace")
    assert "Pinned Comparator statement, dependency and primitive comparison passed" in transcript
    assert "Pinned Comparator transitive axiom check passed" in transcript
    assert "Lean default kernel replay passed" in transcript
    receipt.update({"statement_equality_proved": True, "permitted_axioms_checked": True, "default_kernel_replay_passed": True})
    receipt["stage"] = "nanoda"
    config = {"use_stdin": True, "permitted_axioms": ALLOWED, "unpermitted_axiom_hard_error": True,
              "nat_extension": True, "string_extension": True, "num_threads": args.nanoda_threads,
              "unsafe_permit_all_axioms": False, "print_success_message": True, "print_axioms": True, "pp_to_stdout": True}
    write_json(work / "nanoda-config.json", config)
    tracked[str(work / "nanoda-config.json")] = sha(work / "nanoda-config.json")
    command = command_prefix(args) + ["/usr/bin/time", "-v", "-o", linux_path(work / "nanoda-resources.txt"),
                                    linux_path(args.nanoda_bin), linux_path(work / "nanoda-config.json")]
    receipt["nanoda"] = run_logged(args, command, work / "logs/nanoda.log", stdin=work / "solution.ndjson")
    transcript = (work / "logs/nanoda.log").read_text(encoding="utf8", errors="replace")
    count = re.search(r"Checked (\d+) declarations with no errors", transcript)
    assert count, "Nanoda did not confirm completed proof replay"
    observed = [n.split(".{")[0] for n in re.findall(r"^axiom ([^\s]+)", transcript, re.M)]
    assert set(observed) <= set(ALLOWED), "Unpermitted axiom in independent replay"
    after = {name: sha(Path(name)) for name in tracked}
    assert tracked == after, "A bound source, artifact, tool or export changed during replay"
    assert capture(args, ["sha256sum", lean]).split()[0] == receipt["runtime"]["compiler_sha256"]
    modular = receipt.get("verification_kind") == "modular"
    receipt.update({"stage": "complete", "independent_nanoda_passed": True,
                    "checked_declarations": int(count[1]), "observed_axioms": observed,
                    "sha256_after_replay": after, "inputs_unchanged": True,
                    "local_single_file_verified": not modular,
                    **({"local_modular_verified": True} if modular else {})})
    write_json(work / "verification.json", receipt)
    print(json.dumps({("local_modular_verified" if modular else "local_single_file_verified"): True,
                      "checked_declarations": int(count[1]),
                      "receipt": str(work / "verification.json"), "official_website_acceptance": False}), flush=True)


def main() -> None:
    if not __debug__:
        raise RuntimeError("Python assertions must remain enabled for fail-closed verification")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solution", type=Path, default=ROOT / "submission/gram-defect-20261014/proof/Solution.lean")
    parser.add_argument("--work-dir", type=Path, default=ROOT / "tmp/single-solution")
    parser.add_argument("--website-repo", type=Path, default=WORKSPACE / "proportion_challenge")
    parser.add_argument("--zeta-repo", type=Path, default=SIBLING / "tmp/zeta23")
    parser.add_argument("--runtime-manifest", type=Path, default=SIBLING / "verification/linux-memory-time-20261010/am/environment/handoff-v3.json")
    parser.add_argument("--package-manifest", type=Path, default=SIBLING / "lake-manifest.json")
    parser.add_argument("--numerator", default="39282451209654051457408555553")
    parser.add_argument("--denominator", default="58319774788300000000000000000")
    parser.add_argument("--distribution", default="Ubuntu")
    parser.add_argument("--lean")
    parser.add_argument("--timeout", type=int, default=3200)
    parser.add_argument("--prepare-only", action="store_true")
    parser.add_argument("--compile-only", action="store_true")
    parser.add_argument("--reuse-compiled", type=Path,
                        help="Existing compile.json, or build directory containing per-module logs/*.json")
    parser.add_argument("--comparator-repo", type=Path, default=SIBLING / "tmp/Comparator")
    parser.add_argument("--exporter-repo", type=Path, default=SIBLING / "tmp/lean4export")
    parser.add_argument("--nanoda-repo", type=Path, default=SIBLING / "tmp/nanoda")
    parser.add_argument("--nanoda-bin", type=Path, default=SIBLING / "tmp/kernel-tools/nanoda-target/release/nanoda_bin")
    parser.add_argument("--nanoda-provenance", type=Path, default=SIBLING / "verification/three-website-declarations-modular-nanoda.json")
    parser.add_argument("--nanoda-sha256")
    parser.add_argument("--nanoda-threads", type=int, choices=[1, 2, 4], default=4)
    args = parser.parse_args()
    args.solution = args.solution.resolve()
    work = args.work_dir.resolve()
    if not work.is_relative_to(WORKSPACE):
        parser.error("Generated outputs must remain in this workspace")
    assert args.numerator.isdecimal() and args.denominator.isdecimal() and int(args.denominator) > 0
    receipt = {"stage": "runtime", "invocation_started_unix": time.time(), "ordinary_single_file_lean_passed": False,
               "statement_equality_proved": False, "default_kernel_replay_passed": False,
               "independent_nanoda_passed": False, "local_single_file_verified": False,
               "official_website_acceptance": False, "submitted": False}
    try:
        lean, package_paths, runtime = trusted_runtime(args)
        args.package_paths = package_paths
        receipt["stage"] = "preparation"
        if args.reuse_compiled:
            prepared, compiled = existing_compile(args, work, runtime)
        else:
            prepared = prepare(args, work, runtime)
            if args.prepare_only:
                return
            paths = [linux_path(work / "lib"), *package_paths]
            receipt["stage"] = "fresh-compilation"
            compiled = []
            receipt["compiled_modules"] = compiled
            for module in ["ChallengeDeps", "ChallengeDeps.CandidateSpec", "Challenge.Candidate", "Solution.Candidate"]:
                receipt["stage"] = "fresh-compilation:" + module
                compiled.append(compile_one(args, lean, paths, work, module))
        receipt.update({**prepared, "lean_path": [linux_path(work / "lib"), *package_paths],
                        "compiled_modules": compiled, "ordinary_single_file_lean_passed": True,
                        "whole_submission_compiled": True})
        write_json(work / "compile.json", receipt)
        print(json.dumps({"ordinary_single_file_lean_passed": True, "receipt": str(work / "compile.json")}), flush=True)
        if not args.compile_only:
            audit_replay(args, work, lean, package_paths, receipt)
    except Exception as error:
        work.mkdir(parents=True, exist_ok=True)
        receipt.update({"failed": True, "local_single_file_verified": False,
                        "error": str(error), "error_type": type(error).__name__})
        write_json(work / "failed-verification.json", receipt)
        write_json(work / "verification.json", receipt)
        raise


if __name__ == "__main__":
    main()
