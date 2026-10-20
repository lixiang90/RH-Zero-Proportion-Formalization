"""Text-only draft-v6 from sealed v5, qualifying three Counting wfun names.

No compiler, exporter, kernel, optimizer, subprocess or network invocation.
"""
import argparse
import ast
import copy
import difflib
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parent
PRIOR = HERE / "draft-v5"
REPAIR = ROOT / "research-goal-20261020-w9a2-counting-repair-v1"
PRIOR_MANIFEST_SHA = "497f905f1742380a38c8f5c93ac293d9a0d67717ea5e89e43067751631fe1527"
REPAIR_MANIFEST_SHA = "0a6488324dd5782a3230427701b733427388b203e422f80f35bd461d44cff230"
MODULE_PATH = "StructuralW9A220261020/Counting.lean"
OLD_SHA = "163fbaae81c9afd492cdfd5c66dd2848f1d1e03ac0af6ae3774a7cc619c631d5"
NEW_SHA = "502aa125cfe2566cdbddc3ede296f17dc58ad63a4a750cb6502b24a237b9050a"
EXPECTED_FLAT_SHA = "a517df6aebde6d136f8b83e06c8be10b3413b8430390f52bd47f04e06f0dce26"
BARE = re.compile(rb"(?<![A-Za-z0-9_.])wfun\b")
QUALIFIED = b"Zeta23Ext.Bridge.wfun"
IMPORT = re.compile(rb"import ([A-Za-z_][A-Za-z0-9_.]*)\r?\n?\Z")


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read(path):
    raw = path.read_bytes()
    raw.decode("utf-8", errors="strict")
    assert not raw.startswith(b"\xef\xbb\xbf")
    return raw


def dump(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def write(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as output:
        output.write(raw)


def row(path, base):
    raw = read(path)
    return {"path": path.relative_to(base).as_posix(), "bytes": len(raw), "sha256": sha(raw)}


def manifest(path, expected):
    assert sha(read(path)) == expected
    data = json.loads(read(path))
    for entry in data["files"]:
        target = (path.parent / entry["path"]).resolve()
        assert target.is_relative_to(path.parent.resolve())
        raw = read(target)
        assert len(raw) == entry["bytes"] and sha(raw) == entry["sha256"]
    return data


def literal(path, name):
    nodes = [node.value for node in ast.parse(read(path)).body if isinstance(node, ast.Assign)
        and any(isinstance(target, ast.Name) and target.id == name for target in node.targets)]
    assert len(nodes) == 1
    return ast.literal_eval(nodes[0])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--freeze-once", required=True, action="store_true")
    parser.parse_args()
    destination = HERE / "draft-v6"
    assert __debug__ and not destination.exists()
    prior_manifest = manifest(PRIOR / "files.json", PRIOR_MANIFEST_SHA)
    repair_manifest = manifest(REPAIR / "files.json", REPAIR_MANIFEST_SHA)
    original = read(PRIOR / "frozen-inputs" / MODULE_PATH)
    repaired = read(REPAIR / MODULE_PATH)
    canonical = read(ROOT / MODULE_PATH)
    assert sha(original) == sha(canonical) == OLD_SHA and sha(repaired) == NEW_SHA
    assert len(original) == 21555 and len(repaired) == 21606
    assert len(BARE.findall(original)) == 3 and not BARE.search(repaired)
    assert original.count(QUALIFIED) == 0 and repaired.count(QUALIFIED) == 3
    assert BARE.sub(QUALIFIED, original) == repaired and repaired.replace(QUALIFIED, b"wfun") == original
    before_lines, after_lines = original.splitlines(keepends=True), repaired.splitlines(keepends=True)
    changed_lines = [index + 1 for index, (old, new) in enumerate(zip(before_lines, after_lines)) if old != new]
    assert len(before_lines) == len(after_lines) and changed_lines == [158, 178, 205]
    for old, new in zip(before_lines, after_lines):
        assert old == new or BARE.sub(QUALIFIED, old) == new
    plan = copy.deepcopy(json.loads(read(PRIOR / "candidate-parameters.json")))
    header = literal(HERE / "freeze_text.py", "HEADER")
    runner = ROOT / "research-goal-20261020-w9a2-verification-preparation-v1/run_verification.py"
    assert sha(read(runner)) == "92cc8dcf3e3c46e76490ba7bfe8d93bc10e331131eaab3b4c3ae500f80ac66a8"
    assert literal(runner, "HEADER") == header
    names = [entry["module"] for entry in plan["source_modules"]]
    imports, parts, modules, origins = [], [], [], []
    for entry in plan["source_modules"]:
        source = REPAIR / entry["path"] if entry["path"] == MODULE_PATH else PRIOR / "frozen-inputs" / entry["path"]
        raw = read(source)
        body = []
        for line in raw.splitlines(keepends=True):
            if line.startswith(b"import "):
                match = IMPORT.fullmatch(line)
                assert match is not None
                name = match[1].decode()
                if name in names:
                    assert names.index(name) < names.index(entry["module"])
                else:
                    imports.append(line)
            else:
                body.append(line)
        retained = b"".join(body)
        parts.append((entry["module"], retained))
        modules.append({"module": entry["module"], "path": entry["path"], "bytes": len(raw), "sha256": sha(raw),
            "retained_non_import_bytes": len(retained), "retained_non_import_sha256": sha(retained)})
        origins.append({"logical_path": entry["path"], "actual_input": row(source, ROOT)})
    result = header + b"import ChallengeDeps.CandidateSpec\n" + b"".join(imports) + b"\n"
    segments = []
    for module, body in parts:
        result += ("\n/- BEGIN FLATTENED MODULE " + module + " -/\n").encode()
        start = len(result)
        result += body
        segments.append({"module": module, "start": start, "end": len(result), "retained_non_import_sha256": sha(body)})
        result += b"\n"
    wrapper = read(PRIOR / "frozen-inputs/public-wrapper.lean.txt")
    result += b"\n" + wrapper
    prior = read(PRIOR / "Solution.lean")
    old_segment = next(entry for entry in plan["body_segments"] if entry["module"] == "StructuralW9A220261020.Counting")
    old_body = prior[old_segment["start"]:old_segment["end"]]
    new_body = next(body for module, body in parts if module == "StructuralW9A220261020.Counting")
    assert BARE.sub(QUALIFIED, old_body) == new_body and new_body.replace(QUALIFIED, b"wfun") == old_body
    assert prior[:old_segment["start"]] + new_body + prior[old_segment["end"]:] == result
    assert len(result) == 1830052 and len(result) - len(prior) == 51 and sha(result) == EXPECTED_FLAT_SHA
    assert result.count(b"\r\n") == prior.count(b"\r\n") == 221
    types = []
    official = read(PRIOR / "frozen-inputs/Challenge.Candidate.lean")
    for name in plan["public_roots"]:
        pattern = rb"(?ms)^theorem " + name.encode() + rb"\s*:\s*(.*?)\s*:= by"
        actual, expected = re.findall(pattern, wrapper), re.findall(pattern, official)
        assert len(actual) == len(expected) == 1 and b"".join(actual[0].split()) == b"".join(expected[0].split())
        types.append({"name": name, "type_sha256": sha(actual[0]), "unchanged_and_official_mod_whitespace": True})
    plan.update(solution_bytes=len(result), solution_sha256=sha(result), source_slack_bytes=2000000-len(result),
        source_modules=modules, body_segments=segments, source_revision="draft-v6-qualified-Bridge-wfun-for-flattened-scope",
        repair_manifest_sha256=REPAIR_MANIFEST_SHA, previous_draft_manifest_sha256=PRIOR_MANIFEST_SHA)
    review = {"scope": "Independent text-only delivery review; no proof evaluation or compiler execution",
        "previous_manifest_rows_verified": len(prior_manifest["files"]), "repair_manifest_rows_verified": len(repair_manifest["files"]),
        "Counting_changed_lines": changed_lines, "byte_delta": 51, "only_change": "Three bare wfun identifiers qualified as Zeta23Ext.Bridge.wfun",
        "Counting_forward_and_reverse_projection_exact": True, "flat_sole_Counting_body_forward_and_reverse_projection_exact": True,
        "four_other_modules_and_whole_wrapper_from_v5_byte_identical": True, "trusted_inputs_identical_to_v5": True,
        "import_plan_unchanged": True, "mathematical_values_data_and_public_wrapper_bytes_unchanged": True,
        "public_statement_types": types, "canonical_Counting_original_preserved": True,
        "all_previous_drafts_preserved": True, "source_bytes": len(result), "source_sha256": sha(result),
        "ordinary_new_Counting_or_Final_pass_claimed": False, "single_file_ordinary_pass_claimed": False,
        "Comparator_passed": False, "independent_kernels_passed": False, "complete_3200s_passed": False,
        "official_accepted": False, "upload_ready": False, "main_round_counter_changed": False,
        "proof_compiler_export_kernel_or_optimizer_runs": 0}
    destination.mkdir()
    for folder in ["frozen-inputs", "trusted"]:
        for source in sorted((PRIOR / folder).rglob("*")):
            if source.is_file():
                relative = source.relative_to(PRIOR).as_posix()
                write(destination / relative, repaired if relative == "frozen-inputs/" + MODULE_PATH else read(source))
    write(destination / "Solution.lean", result)
    write(destination / "candidate-parameters.json", dump(plan))
    write(destination / "source-review.json", dump(review))
    write(destination / "source-origins.json", dump({"scope": "Text source inputs only", "module_inputs": origins,
        "previous_draft_manifest": row(PRIOR / "files.json", ROOT), "Counting_repair_manifest": row(REPAIR / "files.json", ROOT),
        "wrapper": row(PRIOR / "frozen-inputs/public-wrapper.lean.txt", ROOT)}))
    diff = "".join(difflib.unified_diff(prior.decode().splitlines(keepends=True), result.decode().splitlines(keepends=True),
        fromfile="draft-v5/Solution.lean", tofile="draft-v6/Solution.lean"))
    write(destination / "Solution-v5-to-v6.diff", diff.encode())
    manifest(PRIOR / "files.json", PRIOR_MANIFEST_SHA); manifest(REPAIR / "files.json", REPAIR_MANIFEST_SHA)
    assert read(ROOT / MODULE_PATH) == canonical
    write(destination / "files.json", dump({"scope": "Unverified source preparation only", "files":
        [row(path, destination) for path in sorted(destination.rglob("*")) if path.is_file()]}))
    print(json.dumps({"version": "draft-v6", "solution_bytes": len(result), "solution_sha256": sha(result),
        "manifest_sha256": sha(read(destination / "files.json")), "source_slack_bytes": 2000000-len(result),
        "upload_ready": False, "proof_compiler_export_kernel_or_optimizer_runs": 0}), flush=True)


if __name__ == "__main__":
    main()
