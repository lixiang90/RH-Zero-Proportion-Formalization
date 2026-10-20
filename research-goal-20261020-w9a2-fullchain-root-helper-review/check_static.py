"""Read/parse frozen sources and existing pins; never import or run their code."""
import ast
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def pin(path):
    raw = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "bytes": len(raw),
        "sha256": hashlib.sha256(raw).hexdigest()}


def load(path):
    return json.loads(path.read_bytes())


def save(name, obj):
    with (HERE / name).open("xb") as stream:
        stream.write((json.dumps(obj, ensure_ascii=False, indent=2) + "\n").encode())


def main():
    paths = [ROOT / name for name in [
        "research-goal-20261020-w9a2-runtime/prepare_fullchain_request.py",
        "research-goal-20261020-w9a2-fullchain-gate-preparation-v1/assemble_gate.py",
        "research-goal-20261020-w9a2-fullchain-gate-preparation-v1/prepared-files.json",
        "research-goal-20261020-w9a2-fullchain-request-preparation/request-proposal.json",
        "research-goal-20261016/gates/w9a2-ordinary-v1b-20261020.json",
        "research-goal-20261020-w9a2-delivery/draft-v5/candidate-parameters.json",
        "research-goal-20261020-w9a2-delivery/draft-v5/Solution.lean",
        "research-goal-20261020-w9a2-delivery/draft-v5/files.json",
        "research-goal-20261020-w9a2-runtime-closure-v5/assemble.py",
        "research-goal-20261020-w9a2-verification-preparation-v1/run_verification.py",
    ]]
    before = [pin(path) for path in paths]
    helper = paths[0].read_text("utf-8")
    tree = ast.parse(helper)
    ast.parse(paths[1].read_text("utf-8"))
    assert pin(paths[1])["sha256"] == "588c1812de91886e5fdfd14f44d3f75485f11ab06e552553b18968a747c1899c"
    assert pin(paths[2])["sha256"] == "e16ef51b40b0ed7618857095330724061801ae4cc364ce3a0622c7c0bec90da3"
    assert pin(paths[3])["sha256"] == "02ec0bc362f17cd5f6a7fe53516f4d20306770bc1f20d4b31958b5fd66f88ff9"
    assert pin(paths[4])["sha256"] == "92def59e80c77b461e3cc301bff748f65e44d53b4c031d745098b156882a3bc5"
    assert pin(paths[7])["sha256"] == "497f905f1742380a38c8f5c93ac293d9a0d67717ea5e89e43067751631fe1527"
    assert pin(paths[6])["sha256"] == "650ad1762ee36ba1ddf5f6a027900b20f0f85ba087ac099fd2c99a54eaf6ae13"
    plan = load(paths[5])
    assert plan["solution_bytes"] == paths[6].stat().st_size == 1830001
    assert plan["solution_sha256"] == pin(paths[6])["sha256"]
    fixed_path = "stage['gate']['path']='research-goal-20261016/gates/w9a2-ordinary-v1b-20261020.json'"
    assert fixed_path in helper
    assert "request['setup_runner']=observation['runner']" in helper
    assert "request['setup_outer_observation']=row(outer)" in helper
    assert "receipt=row(fresh/'leaderboard-receipt.json')" in helper
    assert "body=row(fresh/'leaderboard.json'),maximum_age_seconds=900" in helper
    imports = sorted({node.module for node in ast.walk(tree) if isinstance(node, ast.ImportFrom)} |
        {name.name for node in ast.walk(tree) if isinstance(node, ast.Import) for name in node.names})
    assert imports == ["argparse", "hashlib", "json", "pathlib"]
    assert before == [pin(path) for path in paths]
    report = {
        "scope": "Static source/AST and existing frozen pins only; helper/fullgate/runtime assembler/proof were not executed",
        "definite_blockers_found": [], "result": "PASS_STATIC_INTERFACE_WITH_ACTUAL_EVIDENCE_STILL_PENDING",
        "helper": before[0], "input_pins": before,
        "checks": [
            "v1b gate path matches fixed 92def SHA; other explicit ordinary stages and selected source-bound passes remain frozen template fields",
            "draft-v5 plan/manifest/source pin match 497f/650/1830001; helper copies no proof body and actual fullgate rechecks manifest, score and module sources",
            "runtime/outer arguments replace obsolete prototype closure paths; actual runner row is taken from root outer evidence",
            "helper requires internal terminal and external raw exit0 plus same parent PID; fullgate separately requires exact integer exit0, root owner/protocol role, raw output, actual runner SHA and closure trusted_setup_receipt identity",
            "protocol role stays trusted-runtime-closure-v1 across v5 directory version; completion_receipt must name the actual read-only-setup-receipt.json, never only terminal.json or SDK subreceipt",
            "fresh receipt/body rows and 900s age field match fullgate; fullgate enforces HTTPS official API/raw200/hash/size/age/exact baseline+strict improvement and rechecks age after immutable inputs audit",
            "helper writes only a new request; frozen fullgate produces a disabled proposal requiring separate root authorization before production",
        ],
        "evidence_limits": [
            "Runtime v5 is still active at review; no output, receipt, outer exit or closure completion from that live process was evaluated or upgraded.",
            "No future filled request or fresh HTTP receipt existed in this review scope; their actual values must pass frozen fullgate.",
            "Static compatibility is not production or official verification evidence.",
        ],
        "all_before_after_pins_equal": True, "helper_or_fullgate_runs": 0,
        "runtime_assembler_runs": 0, "compiler_export_kernel_runs": 0,
    }
    save("review.json", report)
    save("files.json", {"files": [pin(path) for path in sorted(HERE.iterdir()) if path.is_file() and path.name != "files.json"],
        "scope": report["scope"], "compiler_export_kernel_runs": 0})
    print(json.dumps({"manifest_sha256": pin(HERE / "files.json")["sha256"], "helper_sha256": before[0]["sha256"],
        "definite_blockers": 0, "compiler_export_kernel_runs": 0}))


if __name__ == "__main__":
    main()
