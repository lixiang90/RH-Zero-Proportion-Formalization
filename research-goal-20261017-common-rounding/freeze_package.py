"""Freeze the global rounding derivation and separate static/metadata audits."""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def row(path):
    raw = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest()}


def check(item, path=None):
    actual = row(path or ROOT / item["path"])
    assert actual["sha256"] == item["sha256"]
    if "bytes" in item:
        assert actual["bytes"] == item["bytes"]
    return actual


def main():
    output = HERE / "rounding-files.json"
    assert not output.exists(), "Preserve frozen package"
    audit1 = ROOT / "research-goal-20261017-common-shift-rounding-audit/rounding-audit-files.json"
    audit2 = ROOT / "research-goal-20261017-common-rounding-independent/audit-files.json"
    assert row(audit1)["sha256"] == "eb0b85e624f2580cd7be593da61327e20be7e23fd16f8b71d94f12c63f63d445"
    assert row(audit2)["sha256"] == "6b7da85247fce6e1680ea0a82d038b2512e587eed5d7bd9013ef6dc298aa3cc8"
    a = json.loads(audit1.read_bytes())
    b = json.loads(audit2.read_bytes())
    assert a["finite_convex_combination_derivation_valid_as_written"]
    assert a["independent_fraction_cutoff_metadata_passed"] and a["maximum_integer_centre"] == 32
    assert b["verdict"] == "correct" and b["construction"]["finite_convex_combination"]
    mapping_file = HERE / "historical-governance-mapping.json"
    mappings = json.loads(mapping_file.read_bytes())["mappings"]
    historical = {m["original_path"]: m for m in mappings}
    assert len(historical) == 3
    dependencies = {}
    for item in a["dependency_files"] + b["sources"]:
        if item["path"] in historical:
            archived = historical[item["path"]]
            actual = check(item, ROOT / archived["snapshot_path"])
            assert actual["sha256"] == archived["sha256"]
            continue
        dependencies[item["path"]] = check(item)
    for item in a["package_files"]:
        check(item)
    check(b["note"])
    budget_path = HERE / "geometry-budget.json"
    budget = json.loads(budget_path.read_bytes())
    assert [case["max_integer_argument"] for case in budget["cases"]] == [32, 32]
    for item in budget["dependency_files"] + [budget["source"]]:
        dependencies[item["path"]] = check(item)
    paths = [HERE / name for name in (
        "NOTE.zh.md", "geometry_budget.py", "geometry-budget.json",
        "historical-governance-mapping.json", "freeze_package.py")]
    paths += [ROOT / m["snapshot_path"] for m in mappings]
    paths += [audit1, audit2, ROOT / b["note"]["path"]]
    paths += [ROOT / item["path"] for item in a["package_files"]]
    files = [row(path) for path in paths]
    result = {"schema": "global-common-shift-rounding-static-evidence-v1",
              "package_files": files, "package_bytes": sum(x["bytes"] for x in files),
              "dependency_files": list(dependencies.values()),
              "historical_governance_sources_not_mutable_math_dependencies": mappings,
              "global_minimizer_condition_correct_on_paper": True,
              "separate_static_mathematical_audits_passed": True,
              "common_feasible_configurations_at_most": 10,
              "fixed_Fin11_zero_padding_allowed": True,
              "both_target_integer_index_budgets_at_most": 32,
              "integer_values_analytically_reproved_here": False,
              "ordinary_integer_gap_translation_family_is_not_the_same": True,
              "necessary_upper_defect_condition_is_not_a_floor_lower_bound": True,
              "can_be_redundant_on_F_below_c_if_all_integer_competitors_have_energy_at_least_c": True,
              "whole_domain_transfer_defect_lower_budget_or_actual_whole_parent_benefit_required": True,
              "new_optimizer_or_solver_calls": 0, "actual_kernel_evaluations": 0,
              "tree_records_read": 0, "Lean_invocations": 0,
              "new_global_floor_proven": False,
              "new_unconditional_zero_proportion_proven": False,
              "website_submission_ready": False,
              "new_Lean_or_optimization_experiment_automatically_authorized": False}
    raw = (json.dumps(result, indent=2) + "\n").encode()
    output.write_bytes(raw)
    print(json.dumps({"manifest_sha256": hashlib.sha256(raw).hexdigest(),
                      "package_files": len(files), "package_bytes": result["package_bytes"]}))


if __name__ == "__main__":
    main()
