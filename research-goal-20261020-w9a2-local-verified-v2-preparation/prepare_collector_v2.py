"""Text-only versioned pin substitution from the frozen reviewed v1 collector.

Does not import or execute either collector, proof, compiler, export or kernel.
"""
import argparse
import ast
import difflib
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
OLD = ROOT / "research-goal-20261020-w9a2-local-verified-preparation"
OLD_SOURCE_SHA = "01b3aa701f79c0b0b6db898dc52bc6159980208a59ebe9a9351f1e5e8e1d9144"
OLD_MANIFEST_SHA = "11d3d3cfd692b2d458aca855704cf078990c9320b4cd82c8083a3186cf9e69ca"
REPLACEMENTS = [
    ("submission/w9a2-weighted-potential-20261020-prepared", "submission/w9a2-weighted-potential-20261020-prepared-v6"),
    ("submission/w9a2-weighted-potential-20261020-expected-wire", "submission/w9a2-weighted-potential-20261020-expected-wire-v6"),
    ("submission/w9a2-weighted-potential-20261020-local-verified", "submission/w9a2-weighted-potential-20261020-local-verified-v2"),
    ("650ad1762ee36ba1ddf5f6a027900b20f0f85ba087ac099fd2c99a54eaf6ae13", "a517df6aebde6d136f8b83e06c8be10b3413b8430390f52bd47f04e06f0dce26"),
    ("e6ae96f6b1d9f971217975eb13e6c0a9a37b219e8d695c4437e89d470db691a8", "3ebcc3b75ee2a75775281a2a0e9321f7610baddcab5965fcf002fd51e2d763fd"),
    ("980fb14e136c86fa66294dec2e00c177cd195919a7a7f472352b38fa836c1849", "55c28b9f90515324f40144822d9e84b301fe9001ec1a03e8df2bf1350159522f"),
    ("0809d39a37ef2130b502fe6278915d083dee17245292de72b11b16507e1e5960", "f81666062165a2a1e60bd59b88cedcc237e72bebe9faca0f183b021fec636851"),
    ("bc1358811491f5fad09f4661f5930bfbe2e4d389c67b661efb17cb81bbadeebb", "e76462f687d4e95d7f9f2ebb558bd5d2d5452814f01e54fd657856dbb12157d1"),
    ("fullchain-v1", "fullchain-v2"), ("68653", "68962"), ("48644", "49320"),
    ("8988.234", "11264.218"), ("1830001", "1830052"), ("frozen650", "frozena517"), ("源码650", "源码a517"),
]


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def pin(path):
    raw = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "bytes": len(raw), "sha256": sha(raw)}


def load(path):
    return json.loads(path.read_bytes())


def write(name, raw):
    with (HERE / name).open("xb") as output:
        output.write(raw)


def manifest(directory, expected):
    assert sha((directory / "files.json").read_bytes()) == expected
    value = load(directory / "files.json")
    for row in value["files"]:
        source = (directory / row["path"]).resolve()
        assert source.is_relative_to(directory.resolve())
        assert source.stat().st_size == row["bytes"] and sha(source.read_bytes()) == row["sha256"]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--freeze-once", required=True, action="store_true")
    parser.parse_args()
    assert __debug__ and not (HERE / "collect_local_verified.py").exists()
    manifest(OLD, OLD_MANIFEST_SHA)
    original = (OLD / "collect_local_verified.py").read_bytes()
    assert sha(original) == OLD_SOURCE_SHA
    revised = original
    rules = []
    for old, new in REPLACEMENTS:
        before, after = old.encode(), new.encode()
        count = revised.count(before)
        assert count > 0, old
        revised = revised.replace(before, after)
        rules.append({"old": old, "new": new, "replacement_count": count})
    reversed_source = revised
    for old, new in reversed(REPLACEMENTS):
        reversed_source = reversed_source.replace(new.encode(), old.encode())
    assert reversed_source == original
    ast.parse(revised)
    prepared = ROOT / "submission/w9a2-weighted-potential-20261020-prepared-v6"
    wire = ROOT / "submission/w9a2-weighted-potential-20261020-expected-wire-v6"
    assert len(manifest(prepared, REPLACEMENTS[5][1])["files"]) == 13
    assert len(manifest(wire, REPLACEMENTS[6][1])["files"]) == 2
    source = prepared / "proof/Solution.lean"
    assert source.stat().st_size == 1830052 and sha(source.read_bytes()) == REPLACEMENTS[3][1]
    actual_start = ROOT / "tmp/w9a2-20261020/fullchain-v2/started.json"
    start = load(actual_start)
    assert start["pid"] == 49320 and start["monotonic_t0"] == 11264.218 and start["gate_sha256"] == REPLACEMENTS[4][1]
    gate = ROOT / "research-goal-20261016/gates/w9a2-fullchain-v2-20261020.json"
    assert sha(gate.read_bytes()) == REPLACEMENTS[4][1]
    assert not (ROOT / "submission/w9a2-weighted-potential-20261020-local-verified-v2").exists()
    write("collect_local_verified.py", revised)
    diff = "".join(difflib.unified_diff(original.decode().splitlines(keepends=True), revised.decode().splitlines(keepends=True),
        fromfile="frozen-v1/collect_local_verified.py", tofile="prepared-v2/collect_local_verified.py"))
    write("exact-source-diff.patch", diff.encode())
    report = {"scope": "Only fixed source/path/process pins substituted from reviewed frozen collector; new collector never executed",
        "old_manifest": pin(OLD / "files.json"), "old_source": pin(OLD / "collect_local_verified.py"),
        "new_source": pin(HERE / "collect_local_verified.py"), "replacement_rules": rules, "forward_and_reverse_exact": True,
        "actual_original_started_metadata": pin(actual_start), "actual_execution_gate": pin(gate),
        "new_prepared_manifest": pin(prepared / "files.json"), "new_wire_manifest": pin(wire / "files.json"),
        "new_source_file": pin(source), "original_session": 68962, "original_parent_pid": 49320,
        "old_failed_v1_accepted_by_new_collector": False, "collector_executed": False, "future_destination_created": False,
        "production_result_claimed": False, "proof_compiler_export_kernel_or_runtime_assembler_runs": 0}
    write("preparation.json", (json.dumps(report, ensure_ascii=False, indent=2) + "\n").encode())
    manifest(OLD, OLD_MANIFEST_SHA)
    print(json.dumps({"new_collector_sha256": sha(revised), "byte_delta": len(revised)-len(original),
        "replacement_rule_count": len(rules), "collector_executed": False, "proof_runs": 0}), flush=True)


if __name__ == "__main__":
    main()
