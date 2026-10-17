"""Freeze this completed, zero-merge audit without rerunning any search.

Existing manifests must match exactly; no pinned input or output is changed.
Large reconstructed JSON/gzip inputs are recorded but not required for upload.
"""
from pathlib import Path
from fractions import Fraction
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def row(path):
    raw = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(),
            "sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw)}


def verify(entries):
    for expected in entries:
        actual = row(ROOT / expected["path"])
        assert all(actual[k] == expected[k] for k in ("sha256", "bytes")), expected["path"]


def main():
    audit = json.loads((HERE.parent / "w10-size-audit-20261017/audit-files.json").read_bytes())
    verify(audit["files"])
    independent = json.loads((HERE / "independent-merge-files.json").read_bytes())
    verify(independent["package_files"] + independent["dependency_files"])
    restore = json.loads((HERE / "restore-inputs.json").read_bytes())
    names = ["bottom_up_merge.py", "merged-summary.json", "README.md",
             "restore_inputs.py", "restore-inputs.json", "freeze_package.py",
             "independent-merge-files.json"]
    names += [Path(r["path"]).name for r in independent["package_files"]]
    names += [part["name"] for output in restore["outputs"] for part in output["parts"]]
    files = [row(HERE / name) for name in sorted(set(names))]
    assert max(r["bytes"] for r in files) <= 4 * 1024 * 1024
    outputs = [row(HERE / r["name"]) for r in restore["outputs"]]
    for r, expected in zip(outputs, restore["outputs"]):
        assert r["sha256"] == expected["sha256"] and r["bytes"] == expected["bytes"]
    threshold = Fraction(242125948973912479045633901091386938489600910650924364438067713,
                         28009683941039967632979924905692003148800000000000000000000000000)
    floor = Fraction(86450000, 10**10)
    assert floor > threshold
    receipt = json.loads((HERE / "independent-merge-replay.json").read_bytes())
    assert receipt["strictly_merged_parent_leaves"] == 0
    assert receipt["minimum_exact_margin"] == "2623983786731307008"
    out = {
        "scope": "Frozen one-pass original-W10 witness reuse experiment: zero merges, complete independent integer replay, no new Lean invocation or exclusion.",
        "files": files,
        "rebuildable_not_required_for_upload": outputs,
        "archive_restore_manifest": row(HERE / "restore-inputs.json"),
        "restoration_command": "python -B -X utf8 research-goal-20261016/w10-size-merge-20261017/restore_inputs.py",
        "independent_replay_command": "python -B -X utf8 research-goal-20261016/w10-size-merge-20261017/independent_merge_replay.py research-goal-20261016/w10-size-merge-20261017/merged-tree.json.gz",
        "frozen_dependencies": [row(HERE.parent / "w10-size-audit-20261017/audit-files.json"),
                                row(HERE / "independent-merge-files.json")],
        "original_floor_parent_tests": 95778,
        "successful_parent_merges": 0,
        "retained_numeric_leaves": 95615,
        "retained_empty_leaves": 163,
        "retained_reflection_leaves": 1,
        "lower_floor_pilot_parent_tests": 1000,
        "lower_floor_full_pass_run": False,
        "lower_floor_goal_arithmetic": {
            "required_floor_strictly_greater_than": str(threshold),
            "fixed_candidate_floor": str(floor),
            "candidate_exceeds_required_threshold": True,
            "conditional_kappa": "3338842690820594373879991756052499665323/4956775000000000000000000000000000000000",
            "conditional_percent_approximation": "67.35917387455744",
            "global_floor_proved": False},
        "independent_full_integer_replay_passed": True,
        "independent_replay_receipt": row(HERE / "independent-merge-replay.json"),
        "producer_summary_records_historical_pre_replay_status": True,
        "known_retained_single_Lean_source_bytes": 4004458,
        "budgeted_source_bytes_including_future_decoder": 4132458,
        "new_Lean_invocations": 0,
        "new_Lean_decoder_verified": False,
        "complete_W10_cover_Lean_proven": False,
        "website_two_MB_source_achieved": False,
        "new_zero_proportion_proven": False,
    }
    raw = (json.dumps(out, indent=2, ensure_ascii=False, allow_nan=False) + "\n").encode("utf8")
    target = HERE / "merge-files.json"
    if target.exists():
        assert target.read_bytes() == raw, "Frozen manifest differs; use a new path instead."
    else:
        target.write_bytes(raw)
    print(json.dumps({"manifest": row(target), "retained_files": len(files),
                      "retained_bytes": sum(r["bytes"] for r in files),
                      "max_upload_bytes": max(r["bytes"] for r in files),
                      "rebuildable_inputs": len(outputs), "all_checked_hashes_match": True}))


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Assertions must remain enabled")
    main()
