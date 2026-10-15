"""Fresh modular and upload verification with pinned archive provenance.

Run under the prepared Linux runtime (Windows users invoke this via WSL):
  python3 scripts/verify_record_20261015.py --prepare-only
  python3 scripts/verify_record_20261015.py --resume

Each overlay has only freshly compiled local modules plus pinned package
paths. The existing verify_single_solution driver supplies the Comparator,
Lean default-kernel replay and independent nanoda stages. Git checkouts are
not claimed: source blobs are read directly from SHA256-bound HTTPS archives.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import tarfile
import time

import verify_single_solution as base

ROOT = Path(__file__).resolve().parents[1]
SETUP = ROOT / "tmp/setup-20261015"
WEBSITE = ROOT / "verification/gram-defect-20261015/website-snapshot"
MODULES = ["GramDefect20261015.Core", "GramDefect20261015.SharpWindow",
           "GramDefect20261015.RefinedCounting", "GramDefect20261015.Final"]
SIMPLE_ROOTS = ["candidate_simple_bound", "candidate_simple_bound_cumulative"]
P = "3338957652820594373879991756052499665323"
Q = "4957023073704306225950000000000000000000"
PREVIOUS = Fraction(834739413205148593469931805501689594457,
                    1239255769294131601825000000000000000000)
ARCHIVES = {
    "Zeta23": "6d49328a1b822637c1b035d30fd4c801b29c28bfcbd6cfcd772863bcbcb318a3",
    "mathlib": "0d44640e4a47b76187c0d6d31800a2e8c05001629c75010cff4c21031f5fa8b3",
    "Comparator": "73649fb6a9d4ff5efed8d5bc5b73f243398f9d95ac81a8dc24f6f51d513be94e",
    "lean4export": "e1a22bb11b1fff7bcf36fd1546c11d36ca0a72601d81b08e65673469d54e0003",
    "nanoda": "f84eb185d4a5594aad18e4b8adbac636e3ace08b671d705dbd6acdbfb834eae6",
}
SITE_HASHES = {
    "challenge/contract.json": "39e1b5a99889cf2c50865883d2007df949bcfced107c92917fe9cd3ab6441020",
    "data/live-records.json": "3b31e6ba6e4666eba217678ded3a5748435f6dbe082d9e0f159351396dba1695",
    "live-head.json": "7882f32b1acd2661a8a965f52921a132292faf2a9bc3991c5ed6faf6ec17b2a5",
    "challenge/templates/CandidateSpec.lean.tmpl": "0e85c8c6b123eec25597fb1e838c632214d3aeb0f2ed8e40ab2890df3ece807c",
    "challenge/templates/Challenge.Candidate.lean": "e77513b7751460054be21697d06b5ffff142d109b65b131e392aa568ccf22378",
}


def archive_blob(name: str, path: str) -> bytes:
    archive = SETUP / (name + ".tar.gz")
    assert base.sha(archive) == ARCHIVES[name], (name, "archive changed")
    with tarfile.open(archive, "r:gz") as stream:
        members = [m for m in stream.getmembers() if m.isfile()
                   and "/".join(Path(m.name).parts[1:]) == path]
        assert len(members) == 1, (name, path)
        return stream.extractfile(members[0]).read()


def runtime(args):
    handoff = json.loads(args.runtime_manifest.read_text(encoding="utf8"))
    sources = json.loads(args.sources_manifest.read_text(encoding="utf8"))
    source_map = {entry["name"]: entry for entry in sources}
    assert sources == handoff["source_archives"]
    for name, digest in ARCHIVES.items():
        assert source_map[name]["commit"] == base.PINS[name]
        assert source_map[name]["archive_sha256"] == digest
        assert base.sha(SETUP / (name + ".tar.gz")) == digest
    lean = handoff["lean"]
    version = base.capture(args, [lean, "--version"])
    compiler_hash = base.capture(args, ["sha256sum", lean]).split()[0]
    assert base.TOOLCHAIN in version
    assert compiler_hash == handoff["lean_sha256"] == \
        "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
    assert handoff["compiler_archive_sha256"] == \
        "48010c7d6264dc992574e9b0e09ece1f9c648e8f5106066b2cdb6834a6a60a6c"
    paths = handoff["lean_path"].split(":")
    assert paths and all("/.lake/packages/" in path for path in paths)
    assert all(Path(path).is_dir() for path in paths)
    args.package_paths = paths
    args.package_root = Path(handoff["package_root"])
    manifest = json.loads(args.package_manifest.read_text(encoding="utf8"))
    revisions = {p["name"]: p["rev"] for p in manifest["packages"]}
    assert all(revisions[name] == base.PINS[name] for name in ["mathlib", "Zeta23"])
    dependency_hash = None
    dependency_modules = []
    if args.dependencies_manifest.exists():
        dependencies = json.loads(args.dependencies_manifest.read_text(encoding="utf8"))
        assert dependencies["passed"] is True and dependencies["cache"]["exit_code"] == 0
        assert dependencies["runtime_manifest_sha256"] == base.sha(args.runtime_manifest)
        dependency_modules = dependencies["compiled_modules"]
        compiled_names = {entry["module"] for entry in dependency_modules}
        assert len(dependency_modules) >= 135 and len(compiled_names) == len(dependency_modules)
        direct_zeta_imports = set(re.findall(r"^import\s+(Zeta23(?:\.[A-Za-z_0-9]+)+)",
            (ROOT / "GramDefect20261015/Core.lean").read_text(encoding="utf8"), re.M))
        assert direct_zeta_imports <= compiled_names, ("Missing explicit Core imports", direct_zeta_imports - compiled_names)
        for entry in dependency_modules:
            source, output = Path(entry["source"]), Path(entry["olean"])
            assert source.is_relative_to(args.package_root / "Zeta23")
            assert output.is_relative_to(args.package_root / "Zeta23/.lake/build/lib/lean")
            relative = source.relative_to(args.package_root / "Zeta23")
            assert hashlib.sha256(archive_blob("Zeta23", str(relative))).hexdigest() == entry["source_sha256"]
            assert entry["exit_code"] == 0 and entry["source_unchanged"]
            assert base.sha(source) == entry["source_sha256"] and base.sha(output) == entry["olean_sha256"]
            assert lean in entry["command"]
        dependency_hash = base.sha(args.dependencies_manifest)
    else:
        assert args.prepare_only, "Fresh pinned dependency build has not completed"
    for name in base.PINS:
        if name in source_map:
            assert source_map[name]["commit"] == base.PINS[name]
    return lean, paths, {
        "compiler": lean, "compiler_version": version, "compiler_sha256": compiler_hash,
        "runtime_manifest_sha256": base.sha(args.runtime_manifest),
        "sources_manifest_sha256": base.sha(args.sources_manifest),
        "package_manifest_sha256": base.sha(args.package_manifest),
        "dependency_basis": "Pinned HTTPS source archives, official Mathlib cache; completed fresh Zeta23 receipt required for compilation",
        "dependency_build_receipt_sha256": dependency_hash,
        "dependency_compiled_modules": dependency_modules,
        "git_checkout_claimed": False, "source_archives": sources,
    }


def copy_tools(args, work):
    tools = work / "tools"
    for folder in ["source", "logs", "lib"]:
        (tools / folder).mkdir(parents=True, exist_ok=True)
    provenance = {}
    expected_sources = {"CoreAudit.lean"}
    names_by_package = {
        "lean4export": ["Export.lean", "Export/Parse.lean", "Main.lean"],
        "Comparator": ["Comparator.lean", "Comparator/Axioms.lean",
                       "Comparator/Compare.lean", "Comparator/Util.lean", "Main.lean"],
    }
    for package, names in names_by_package.items():
        for name in names:
            data = archive_blob(package, name)
            assert (args.package_root / package / name).read_bytes() == data
            output = ("ExporterMain.lean" if package == "lean4export" else "ComparatorMain.lean") \
                if name == "Main.lean" else name
            target = tools / "source" / output
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            expected_sources.add(output)
            provenance[str(target.relative_to(work))] = {
                "source_kind": "Pinned HTTPS archive", "commit": base.PINS[package],
                "archive_sha256": ARCHIVES[package], "archive_path": name,
                "source_sha256": base.sha(target),
            }
    manifest = json.loads(archive_blob("Comparator", "lake-manifest.json"))
    assert any(p["name"] == "lean4export" and p["rev"] == base.PINS["lean4export"]
               for p in manifest["packages"])
    build = json.loads(args.nanoda_provenance.read_text(encoding="utf8"))
    assert build["exit_code"] == 0 and build["source_commit"] == base.PINS["nanoda"]
    assert Path(build["binary"]) == args.nanoda_bin
    assert base.sha(args.nanoda_bin) == build["binary_sha256"] == \
        "0c8332aae13164943ebfed4f8f4ed969494d8e85edff9d774a70fd92ea9318c2"
    assert hashlib.sha256(archive_blob("nanoda", "Cargo.lock")).hexdigest() == build["cargo_lock_sha256"]
    args.nanoda_sha256 = build["binary_sha256"]
    provenance["nanoda_binary"] = {**build, "source_archive_sha256": ARCHIVES["nanoda"],
                                   "build_receipt_sha256": base.sha(args.nanoda_provenance)}
    driver = ROOT / "tools/ComparatorCoreAudit.lean"
    (tools / "source/CoreAudit.lean").write_bytes(driver.read_bytes())
    provenance["core_driver"] = {"path": str(driver), "sha256": base.sha(driver)}
    assert {str(path.relative_to(tools / "source")) for path in (tools / "source").rglob("*.lean")} == expected_sources
    validate_overlay(tools, base.topological_modules(tools))
    return tools, provenance


def validate_overlay(work, modules):
    allowed = {str(Path(*module.split(".")).with_suffix(".olean")) for module in modules}
    present = {str(path.relative_to(work / "lib")) for path in (work / "lib").rglob("*.olean")}
    assert present <= allowed, ("Unexpected overlay module shadows trusted packages", sorted(present - allowed))


def extra_challenge() -> str:
    result = "\nnoncomputable section\n"
    for name, cumulative in zip(SIMPLE_ROOTS, [False, True]):
        a, b = ("0", "T") if cumulative else ("T", "(2 * T)")
        result += (f"theorem {name} : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,\n"
                   f"  (candidateKappa - ε) * (Zeta23.Ncount {a} {b} : ℝ) ≤ "
                   f"Zeta23.N0simple {a} {b} := by sorry\n")
    return result + "end\n"


def modular_solution() -> str:
    text = "import GramDefect20261015.Final\nimport ChallengeDeps.CandidateSpec\nnoncomputable section\n"
    text += "namespace RecordModularCounts\n"
    text += "theorem count_eq (a b : ℝ) : _root_.Ncount a b = Zeta23.Ncount a b := by rfl\n"
    text += "theorem distinct_eq (a b : ℝ) : _root_.N0star a b = Zeta23.N0star a b := by rfl\n"
    text += "end RecordModularCounts\n"
    text += "theorem candidate_strict_improvement : currentRecordKappa < candidateKappa := by\n"
    text += "  norm_num [currentRecordKappa, candidateKappa]\n"
    for name, theorem, simple, cumulative in [
        (base.ROOTS[1], "distinct_dyadic", False, False),
        (base.ROOTS[2], "distinct_cumulative", False, True),
        (SIMPLE_ROOTS[0], "simple_dyadic", True, False),
        (SIMPLE_ROOTS[1], "simple_cumulative", True, True),
    ]:
        a, b = ("0", "T") if cumulative else ("T", "(2 * T)")
        count = "Zeta23.N0simple" if simple else "N0star"
        total = "Zeta23.Ncount" if simple else "Ncount"
        text += (f"theorem {name} : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,\n"
                 f"  (candidateKappa - ε) * ({total} {a} {b} : ℝ) ≤ {count} {a} {b} := by\n"
                 "  simpa only [candidateKappa, GramDefect20261015.recordRatio,\n"
                 "    RecordModularCounts.count_eq, RecordModularCounts.distinct_eq] using\n"
                 f"    GramDefect20261015.{theorem}\n")
    return text + "end\n"


def prepare(args, work, runtime_info, kind):
    if work.exists() and any(work.iterdir()) and not args.resume:
        raise ValueError("Fresh verification requires empty work directory; use --resume for hash-checked reuse")
    for folder in ["source/ChallengeDeps", "source/Challenge", "source/Solution", "lib", "logs"]:
        (work / folder).mkdir(parents=True, exist_ok=True)
    expected_modules = ["ChallengeDeps", "ChallengeDeps.CandidateSpec", "Challenge.Candidate",
                        "Solution.Candidate", *([] if kind == "single" else MODULES)]
    validate_overlay(work, expected_modules)
    repo_paths = [Path(__file__).resolve(), Path(base.__file__).resolve(), args.upload,
                 args.sources_manifest, args.runtime_manifest, args.nanoda_provenance,
                 *[ROOT / Path(*module.split(".")).with_suffix(".lean") for module in MODULES]]
    if args.dependencies_manifest.exists():
        repo_paths.append(args.dependencies_manifest)
        for entry in runtime_info["dependency_compiled_modules"]:
            repo_paths.extend([Path(entry["source"]), Path(entry["olean"])])
    bound_inputs = {str(path): base.sha(path) for path in repo_paths}
    site = args.website_repo
    for name, digest in SITE_HASHES.items():
        assert base.sha(site / name) == digest, (name, "website evidence changed")
    contract = json.loads((site / "challenge/contract.json").read_text(encoding="utf8"))
    assert contract["trustedUpstream"]["commit"] == base.PINS["Zeta23"]
    assert contract["trustedUpstream"]["mathlibCommit"] == base.PINS["mathlib"]
    for key, package in [("comparatorCommit", "Comparator"), ("lean4exportCommit", "lean4export"), ("nanodaCommit", "nanoda")]:
        assert contract["verifier"][key] == base.PINS[package]
    rows = json.loads((site / "data/live-records.json").read_text(encoding="utf8"))
    current = [r for r in rows if r["status"] == "kernel-verified" and r["track"] == "critical-line"][-1]
    old = Fraction(int(current["exactRational"]["numerator"]), int(current["exactRational"]["denominator"]))
    assert old == PREVIOUS and Fraction(int(P), int(Q)) > old
    (work / "source/ChallengeDeps.lean").write_bytes(archive_blob("Zeta23", "comparator/ChallengeDeps.lean"))
    spec = (site / "challenge/templates/CandidateSpec.lean.tmpl").read_text(encoding="utf8")
    spec = spec.replace("{{CURRENT_EXPRESSION}}", current["exactExpression"]).replace("{{NUMERATOR}}", P).replace("{{DENOMINATOR}}", Q)
    (work / "source/ChallengeDeps/CandidateSpec.lean").write_text(spec, encoding="utf8", newline="\n")
    challenge = (site / "challenge/templates/Challenge.Candidate.lean").read_text(encoding="utf8")
    if kind == "modular":
        challenge = "import Zeta23.FinalMult\n" + challenge + extra_challenge()
        for module in MODULES:
            relative = Path(*module.split(".")).with_suffix(".lean")
            target = work / "source" / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((ROOT / relative).read_bytes())
        data = modular_solution().encode("utf8")
    else:
        data = args.upload.read_bytes()
        assert len(data) <= 2_000_000
        mask = __import__("bundle_gram_defect_solution").code_mask(data.decode("utf8"))
        assert not re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", mask)
    (work / "source/Challenge/Candidate.lean").write_text(challenge, encoding="utf8", newline="\n")
    (work / "source/Solution/Candidate.lean").write_bytes(data)
    assert {str(path.relative_to(work / "source")) for path in (work / "source").rglob("*.lean")} == {
        str(Path(*module.split(".")).with_suffix(".lean")) for module in expected_modules}
    receipt = {"scope": "Fresh " + kind + " local verification; no website upload", "verification_kind": kind,
        "runtime": runtime_info, "pins": base.PINS, "solution": str(work / "source/Solution/Candidate.lean"),
        "solution_sha256": hashlib.sha256(data).hexdigest(), "solution_bytes": len(data),
        "upload": str(args.upload), "upload_sha256": base.sha(args.upload),
        "score": {"numerator": P, "denominator": Q}, "current_record": current,
        "website_source_commit": "db30e9dacf9278759aa77719eb201887317b7928",
        "website_source_sha256": SITE_HASHES,
        "additional_bound_source_sha256": bound_inputs,
        "generated_source_sha256": {str(p.relative_to(work)): base.sha(p) for p in (work / "source").rglob("*.lean")},
        "ordinary_single_file_lean_passed": False, "local_single_file_verified": False,
        "statement_equality_proved": False, "independent_nanoda_passed": False,
        "default_kernel_replay_passed": False, "official_website_acceptance": False, "submitted": False}
    base.write_json(work / "prepared.json", receipt)
    assert bound_inputs == {name: base.sha(Path(name)) for name in bound_inputs}
    return receipt


def compile_module(args, lean, paths, work, module, compiled):
    record_path = work / "logs" / (module + ".json")
    source = work / "source" / Path(*module.split(".")).with_suffix(".lean")
    dependencies = {entry["module"]: entry["olean_sha256"] for entry in compiled}
    if args.resume and record_path.exists():
        old = json.loads(record_path.read_text(encoding="utf8"))
        output = Path(old["olean"])
        expected_output = work / "lib" / Path(*module.split(".")).with_suffix(".olean")
        assert output.resolve() == expected_output.resolve(), "Unexpected prior output path"
        assert Path(old["source"]).resolve() == source.resolve(), "Unexpected prior source path"
        if old["exit_code"] == 0 and old["source_unchanged"] and output.exists() \
                and old["source_sha256"] == base.sha(source) and old["olean_sha256"] == base.sha(output) \
                and old.get("local_dependency_olean_sha256") == dependencies \
                and old.get("compile_runtime_basis") == args.compile_runtime_basis:
            assert lean in old["command"]
            assert "LEAN_PATH=" + ":".join(paths) in old["command"]
            assert str(source) in old["command"] and str(output) in old["command"]
            old["reused_prior_compile"] = True
            return old
    for path in [record_path, work / "logs" / (module + ".log")]:
        if path.exists():
            suffix = 1
            while path.with_name(path.name + f".attempt{suffix}").exists():
                suffix += 1
            path.rename(path.with_name(path.name + f".attempt{suffix}"))
    result = base.compile_one(args, lean, paths, work, module)
    result["local_dependency_olean_sha256"] = dependencies
    result["compile_runtime_basis"] = args.compile_runtime_basis
    base.write_json(record_path, result)
    return result


def verify(args, lean, packages, info, kind):
    work = args.work_dir / kind
    receipt = {"stage": "preparation", "verification_kind": kind}
    try:
        receipt = prepare(args, work, info, kind)
        if args.prepare_only:
            return receipt
        paths = [str(work / "lib"), *packages]
        modules = ["ChallengeDeps", "ChallengeDeps.CandidateSpec", "Challenge.Candidate"]
        if kind == "modular":
            modules += MODULES
        modules += ["Solution.Candidate"]
        receipt["compiled_modules"] = []
        for module in modules:
            receipt["stage"] = "compilation:" + module
            receipt["compiled_modules"].append(compile_module(args, lean, paths, work, module,
                                                            receipt["compiled_modules"]))
            base.write_json(work / "compile-progress.json", receipt)
        assert receipt["generated_source_sha256"] == {
            str(p.relative_to(work)): base.sha(p) for p in (work / "source").rglob("*.lean")}
        bound_inputs = receipt["additional_bound_source_sha256"]
        assert bound_inputs == {name: base.sha(Path(name)) for name in bound_inputs}
        receipt.update(stage="compiled", whole_submission_compiled=kind == "single",
                       ordinary_single_file_lean_passed=kind == "single")
        base.write_json(work / "compile.json", receipt)
        if args.compile_only:
            return receipt
        args.solution = work / "source/Solution/Candidate.lean"
        web_roots = base.ROOTS[:]
        if kind == "modular":
            base.ROOTS = [*web_roots, *SIMPLE_ROOTS]
        try:
            base.audit_replay(args, work, lean, packages, receipt)
        finally:
            base.ROOTS = web_roots
        assert bound_inputs == {name: base.sha(Path(name)) for name in bound_inputs}
        receipt["additional_bound_source_sha256"] = bound_inputs
        receipt["local_modular_verified"] = kind == "modular"
        receipt["local_single_file_verified"] = kind == "single"
        base.write_json(work / "verification.json", receipt)
        return receipt
    except Exception as error:
        work.mkdir(parents=True, exist_ok=True)
        receipt.update(failed=True, error=str(error), error_type=type(error).__name__,
                       local_single_file_verified=False, local_modular_verified=False)
        base.write_json(work / "failed-verification.json", receipt)
        base.write_json(work / "verification.json", receipt)
        raise
    finally:
        destination = args.receipt_dir / kind
        destination.mkdir(parents=True, exist_ok=True)
        for path in work.glob("*.json"):
            shutil.copyfile(path, destination / path.name)
        for subdirectory in ["logs", "tools/logs"]:
            for path in (work / subdirectory).glob("*"):
                if path.is_file() and (path.suffix in [".log", ".json"] or ".attempt" in path.name):
                    target = destination / subdirectory / path.name
                    target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(path, target)


def main():
    if os.name == "nt":
        raise SystemExit("Run via WSL python3 so fresh build artifacts stay on the Linux filesystem")
    assert __debug__, "Assertions must remain enabled"
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", type=Path, default=Path("/var/tmp/rh-zero-20261015/record-verification"))
    parser.add_argument("--receipt-dir", type=Path, default=ROOT / "verification/gram-defect-20261015/lean")
    parser.add_argument("--mode", choices=["all", "modular", "single"], default="all")
    parser.add_argument("--runtime-manifest", type=Path, default=SETUP / "runtime.json")
    parser.add_argument("--sources-manifest", type=Path, default=SETUP / "sources.json")
    parser.add_argument("--dependencies-manifest", type=Path, default=SETUP / "dependencies.json")
    parser.add_argument("--website-repo", type=Path, default=WEBSITE)
    parser.add_argument("--upload", type=Path, default=ROOT / "submission/gram-defect-20261015/proof/Solution.lean")
    parser.add_argument("--package-manifest", type=Path, default=ROOT / "lake-manifest.json")
    parser.add_argument("--nanoda-provenance", type=Path, default=SETUP / "nanoda-build.json")
    parser.add_argument("--nanoda-bin", type=Path, default=Path("/var/tmp/rh-zero-20261015/nanoda-target/release/nanoda_bin"))
    parser.add_argument("--nanoda-threads", type=int, choices=[1, 2, 4], default=4)
    parser.add_argument("--timeout", type=int, default=14400)
    parser.add_argument("--prepare-only", action="store_true")
    parser.add_argument("--compile-only", action="store_true")
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args()
    args.work_dir = args.work_dir.resolve()
    args.distribution = "Ubuntu"
    args.nanoda_sha256 = None
    assert args.work_dir.is_relative_to(Path("/var/tmp/rh-zero-20261015"))
    args.work_dir.mkdir(parents=True, exist_ok=True)
    args.receipt_dir.mkdir(parents=True, exist_ok=True)
    pending = {"stage": "running", "all_requested_checks_passed": False,
               "official_website_acceptance": False, "submitted": False}
    base.write_json(args.work_dir / "summary.json", pending)
    base.write_json(args.receipt_dir / "summary.json", pending)
    base.copy_tools = copy_tools
    lean, packages, info = runtime(args)
    args.compile_runtime_basis = {name: info[name] for name in [
        "compiler_sha256", "runtime_manifest_sha256", "sources_manifest_sha256",
        "package_manifest_sha256", "dependency_build_receipt_sha256"]}
    results = {}
    for kind in (["modular", "single"] if args.mode == "all" else [args.mode]):
        results[kind] = verify(args, lean, packages, info, kind)
    summary = {"modes": list(results), "prepared_only": args.prepare_only,
               "compile_only": args.compile_only, "runtime": info,
               "results": {kind: str(args.work_dir / kind / "verification.json") for kind in results},
               "all_requested_checks_passed": not args.prepare_only and not args.compile_only
                   and all(r.get("independent_nanoda_passed") and r.get("statement_equality_proved")
                           and r.get("default_kernel_replay_passed") for r in results.values()),
               "official_website_acceptance": False, "submitted": False}
    base.write_json(args.work_dir / "summary.json", summary)
    args.receipt_dir.mkdir(parents=True, exist_ok=True)
    base.write_json(args.receipt_dir / "summary.json", summary)
    print(json.dumps({"modes": list(results), "prepared_only": args.prepare_only,
        "all_requested_checks_passed": summary["all_requested_checks_passed"],
        "receipt": str(args.receipt_dir / "summary.json"),
        "official_website_acceptance": False}), flush=True)


if __name__ == "__main__":
    main()
