"""Bind the local mixed subtree and graph bridges to ordinary Lean receipts.

This compact index is not an independent-kernel receipt or a global cover.
The canonical per-module receipt and logs remain lean_verification.json.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
PREFIX = "StructuralGoal20261016."


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    receipt_path = HERE / "lean_verification.json"
    receipt = json.loads(receipt_path.read_text())
    known = {item["module"]: item for item in receipt["modules"]}
    names = [
        "WindowFirstOrderCertificate", "WindowCellCuts", "WindowMixedLeaves",
        "WindowMixedContractions", "WindowMixedCover", "WindowCurvatureOracle",
        "WindowCurvatureGridAll", "WindowCurvatureScalar", "WindowCurvatureLeavesAll",
        "WindowCurvatureSubtreeData", "WindowCurvatureOBBT00",
        "WindowCurvatureOBBTDispatch", "WindowCurvatureOBBTGroup00",
        "WindowCurvatureOBBTGroup01", "WindowCurvatureOBBTGroup02",
        "WindowCurvatureOBBTAll", "WindowCurvatureSubtreeGeometry",
        "WindowCurvatureSubtree", "WindowDerivativeGraph", "WindowLiftedFarkas",
    ]
    entries = []
    for name in names:
        module = PREFIX + name
        item = known[module]
        source = ROOT / (module.replace(".", "/") + ".lean")
        log = HERE / item["log"]
        assert item["passed"] and item["source_unchanged"]
        assert digest(source) == item["source_sha256"]
        assert digest(log) == item["log_sha256"]
        assert "sorryAx" not in log.read_text(errors="replace")
        entry = {key: item[key] for key in (
            "module", "source_sha256", "olean_sha256", "log", "log_sha256",
            "whole_process_seconds", "synchronous_elaboration")}
        entry["kind"] = "data_only" if name.endswith("Data") else "proof_module"
        entries.append(entry)
    result = {
        "scope": "Ordinary-kernel local mixed subtree and actual graph soundness. No full pressure-root tree is supplied.",
        "local_root_path": "r00100000110110111000111",
        "local_target_floor_rational": "11/1250",
        "local_subtree": {"actual_obbt_bounds": 24, "splits": 2, "actual_curvature_leaves": 3,
                          "root": PREFIX + "WindowCurvatureSubtree.exclude", "ordinary_kernel_pass": True},
        "source_and_log_hashes_rechecked": True,
        "proof_modules": sum(entry["kind"] == "proof_module" for entry in entries),
        "data_only_modules": sum(entry["kind"] == "data_only" for entry in entries),
        "compiler_sha256": receipt["compiler_sha256"],
        "driver_sha256": receipt["driver_sha256"],
        "index_generator_sha256": digest(Path(__file__)),
        "independent_kernel_verified": False,
        "global_energy_floor_proven": False,
        "unconditional_counting_proven": False,
        "submission_ready": False,
        "modules": entries,
    }
    destination = HERE / "lean_local_mixed_20261017.json"
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"file": destination.name, "sha256": digest(destination),
                      "proof_modules": result["proof_modules"], "local_subtree_pass": True,
                      "global_floor_pass": False}))


if __name__ == "__main__":
    main()
