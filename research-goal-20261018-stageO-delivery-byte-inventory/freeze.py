"""Byte-only sealing of the completed one-pair inventory; no math replay."""
from pathlib import Path
from hashlib import sha256
import ast
import json
import os
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

def digest(data):
    return sha256(data).hexdigest()

def describe(path):
    data = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(),
            "bytes": len(data), "sha256": digest(data)}

def main():
    destination = HERE / "files.json"
    assert not destination.exists(), "immutable absent-output freeze only"
    inventory = json.loads((HERE / "inventory.json").read_text(encoding="utf-8"))
    assert inventory["fixed_G_index"] == 1322606
    dependencies = []
    for relative, expected in inventory["source_and_data_input_sha256"].items():
        item = describe(ROOT / relative)
        assert item["sha256"] == expected, relative
        dependencies.append(item)
    member = inventory["original_record_member"]
    with (ROOT / member["path"]).open("rb") as handle:
        handle.seek(member["offset"])
        data = handle.read(member["bytes"])
    assert len(data) == member["bytes"]
    assert digest(data) == member["compressed_member_sha256"]
    for key, size in [("literal_format", 15950), ("selector_format", 1465)]:
        saved = inventory[key]["source"]
        assert describe(ROOT / saved["path"]) == saved
        assert saved["bytes"] == size
        assert sum(section["utf8_bytes"] for section in inventory[key]["section_bytes"]) == size
    for filename in ["serialize_inventory.py", "freeze.py"]:
        ast.parse((HERE / filename).read_text(encoding="utf-8"), filename=filename)
    owned_names = ["serialize_inventory.py", "LiteralOnePair.lean", "SelectorOnePair.lean",
                   "inventory.json", "NOTE.zh.md", "freeze.py"]
    owned = [describe(HERE / filename) for filename in owned_names]
    result = {
        "schema": "fixed-O-one-pair-source-byte-inventory-files-v1",
        "fixed_G_index": 1322606,
        "owned_files": owned,
        "owned_file_count": len(owned),
        "owned_total_bytes_excluding_manifest": sum(item["bytes"] for item in owned),
        "read_only_whole_file_dependencies": dependencies,
        "read_only_exact_member_dependency": member,
        "freeze_checks": {"source_byte_identity": True, "section_byte_sums": True,
                          "two_Python_ASTs_only": True, "one_member_compressed_hash_only": True},
        "mathematical_evaluations_in_this_freeze": 0,
        "Lean_parser_or_kernel_runs": 0,
        "selector_reconstructor_implemented": False,
        "merged_submission_source_or_runtime_gate_passed": False,
        "one_pair_only_no_extrapolation": True,
        "runtime": {"executable": sys.executable, "version": sys.version},
    }
    encoded = (json.dumps(result, ensure_ascii=False, indent=2, allow_nan=False) + "\n").encode("utf-8")
    with destination.open("xb") as handle:
        handle.write(encoded)
        handle.flush()
        os.fsync(handle.fileno())
    print(json.dumps({"passed": True, "manifest": describe(destination),
                      "owned_files": len(owned),
                      "owned_total_bytes_excluding_manifest": result["owned_total_bytes_excluding_manifest"],
                      "mathematical_evaluations": 0, "Lean_runs": 0}, ensure_ascii=False))

if __name__ == "__main__":
    main()
