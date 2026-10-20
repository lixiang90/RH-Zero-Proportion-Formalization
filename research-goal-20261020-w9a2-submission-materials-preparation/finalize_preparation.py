"""Check the frozen prepared material and record current policy separately.

No file in the frozen submission package is changed. No proof/network calls.
"""
import ast
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PACK = ROOT / "submission/w9a2-weighted-potential-20261020-prepared"


def pin(path):
    raw = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "bytes": len(raw),
        "sha256": hashlib.sha256(raw).hexdigest()}


def load(path):
    return json.loads(path.read_bytes())


def save(name, value):
    with (HERE / name).open("xb") as output:
        output.write((json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode())


def main():
    material_manifest = PACK / "files.json"
    assert pin(material_manifest)["sha256"] == "980fb14e136c86fa66294dec2e00c177cd195919a7a7f472352b38fa836c1849"
    manifest = load(material_manifest)
    checked = []
    for row in manifest["files"]:
        path = PACK / row["path"]
        actual = pin(path)
        assert actual["bytes"] == row["bytes"] and actual["sha256"] == row["sha256"]
        checked.append(actual)
    solution = PACK / "proof/Solution.lean"
    draft = ROOT / "research-goal-20261020-w9a2-delivery/draft-v5/Solution.lean"
    assert solution.read_bytes() == draft.read_bytes()
    assert pin(solution)["sha256"] == "650ad1762ee36ba1ddf5f6a027900b20f0f85ba087ac099fd2c99a54eaf6ae13"
    fields = load(PACK / "website-fields.draft.json")
    status = load(PACK / "verification-status.json")
    assert fields["public_display_name"] == "Li Xiang"
    assert fields["authenticated_GitHub_login"] == "lixiang90"
    assert fields["AI_model_optional"] is None and fields["model_field_value"] == ""
    assert fields["coding_harness_optional"] == "Codex"
    assert len(fields["summary"]) == 605 <= 1000
    assert status["ordinary_modular_complete_actual_Lean_passed"] is True
    assert status["ordinary_printed_root_count"] == len(status["ordinary_printed_axioms"]) == 12
    pending = ["single_file_ordinary_compile_passed", "Comparator_statement_dependency_primitive_passed",
        "Comparator_transitive_axioms_passed", "default_Lean_kernel_replay_passed", "independent_serial_nanoda_passed",
        "complete_single_3200s_production_passed", "official_website_acceptance_confirmed", "upload_ready", "submitted"]
    assert all(status[name] is False for name in pending)
    assert all(set(axioms) <= set(status["allowed_axioms"]) for axioms in status["ordinary_printed_axioms"].values())
    policy = ROOT / "research-goal-20261020-w9a2-source-normalization-review"
    policy_manifest = policy / "files.json"
    assert pin(policy_manifest)["sha256"] == "4209625bb670f556ccabbf3b46a31deed8a67178951d4a8524be551406ec3432"
    for row in load(policy_manifest)["files"]:
        path = ROOT / row["path"]
        actual = pin(path)
        assert actual["bytes"] == row["bytes"] and actual["sha256"] == row["sha256"]
    # Static parsing only; do not import or execute either preparation script.
    for path in [HERE / "prepare_materials.py", HERE / "finalize_preparation.py"]:
        ast.parse(path.read_text("utf-8"), filename=str(path))
    report = {
        "scope": "Read-only final check of frozen prepared submission materials; no proof, compiler, export, kernel, or network call",
        "prepared_material_manifest": pin(material_manifest), "checked_material_files": checked,
        "exact_draft_v5_source": pin(draft), "all_source_bytes_equal": True,
        "public_display_name": "Li Xiang", "GitHub_login": "lixiang90", "model_field": "",
        "wire_model_value_if_official_form_is_used": None, "harness": "Codex", "summary_characters": 605,
        "important_draft_manifest_scope": "submission.draft.json is preparatory metadata, not the server-generated official manifest. Its empty model is a blank UI placeholder; the actual client maps this to JSON null, and the server regenerates its manifest. Use website-fields.draft.json for UI fields; do not upload submission.draft.json as an official manifest.",
        "current_wire_policy_manifest": pin(policy_manifest), "current_wire_policy_report": pin(policy / "review.json"),
        "normalization_preview_scope_correction": "The frozen material's historical_policy_reference describes a historical parallel comparison preview. Current deployed client sends raw solution state; current main server does not trim it. Do not apply trim or newline normalization to source650 on this evidence.",
        "source_wire_policy": "Upload the exact file and avoid editing it in the textarea; verify actual wire source bytes/SHA and labelled manifest+source digest. Raw source contains 221 CRLF and one terminal LF.",
        "ordinary_modular_12_roots_passed": True,
        "single_file_dual_kernel_3200s_official_pending": True,
        "pending_flags": {name: status[name] for name in pending},
        "future_results": "Root must add a separate hash-linked production/official addendum. Never change frozen Solution.lean or relabel pending flags in this package.",
        "frozen_submission_files_modified": False, "proof_compiler_export_kernel_network_calls": 0,
    }
    save("preparation-final-check.json", report)
    files = [pin(path) for path in sorted(HERE.iterdir()) if path.is_file() and path.name != "prepared-files.json"]
    save("prepared-files.json", {"schema": "w9a2-submission-material-preparation-files-v1", "files": files,
        "material_manifest": pin(material_manifest), "wire_policy_manifest": pin(policy_manifest),
        "proof_compiler_export_kernel_network_calls": 0})
    print(json.dumps({"prepared_manifest_sha256": pin(HERE / "prepared-files.json")["sha256"],
        "material_manifest_sha256": pin(material_manifest)["sha256"], "source_sha256": pin(solution)["sha256"],
        "upload_ready": False, "proof_compiler_export_kernel_network_calls": 0}), flush=True)


if __name__ == "__main__":
    main()
