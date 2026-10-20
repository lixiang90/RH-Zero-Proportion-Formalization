"""Exact static derivation: ten proof-only table definitions, no proof execution."""
from pathlib import Path
import difflib
import hashlib
import json
import os
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OLD = HERE.parent / "draft-v7/Solution.lean"
OLD_SHA = "dae01f6844642d7f9ee8180616c1f57aefc18ab8616bc8a4a46a14bf8e9fefc6"
NAMES = tuple(f"PTT_{i}" for i in range(8)) + ("PTT", "PT")
PREVIOUS_NAMES = ("mcheckP", "mleafP", "leafStep", "node", "walkC", "walk", "walkCut", "walkCutR")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def write_new(name, data):
    with (HERE / name).open("xb") as stream:
        stream.write(data); stream.flush(); os.fsync(stream.fileno())


def json_bytes(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def main():
    output_names = ("Solution.lean", "edits.json", "projection.json", "exact-source-diff.patch", "README.txt", "files.json")
    require(not any((HERE / name).exists() for name in output_names), "Exclusive output exists")
    old = OLD.read_bytes()
    require(len(old) == 1829242 and sha(old) == OLD_SHA, "Frozen v7 input mismatch")
    paths = [OLD, OLD.parent / "files.json", ROOT / "research-goal-20261020-w9a2-v7-resource-static-formal/files.json"]
    paths += [HERE.parent / "draft-v6/frozen-inputs/StructuralW9A220261020" / (name + ".lean")
              for name in ("Core", "Graph", "Localization", "Counting", "Final")]
    inputs = [{"path": p.relative_to(ROOT).as_posix(), "bytes": p.stat().st_size, "sha256": sha(p.read_bytes())} for p in paths]
    operations = []
    for name in NAMES:
        matches = list(re.finditer(rb"(?m)^def " + name.encode() + rb"(?=[ \t(])", old))
        require(len(matches) == 1, "Expected exactly one plain declaration: " + name)
        m = matches[0]
        operations.append((m.start(), m.end(), m.group(), b"noncomputable " + m.group(), name))
    operations.sort()
    pieces, edits, gaps = [], [], []
    old_pos, new_pos = 0, 0
    for number, (start, end, before, replacement, name) in enumerate(operations, 1):
        require(start >= old_pos and old[start:end] == before, "Overlapping or inexact operation")
        gap = old[old_pos:start]
        gaps.append({"old_start_byte": old_pos, "old_end_byte_exclusive": start,
                     "new_start_byte": new_pos, "new_end_byte_exclusive": new_pos+len(gap), "bytes": len(gap), "sha256": sha(gap)})
        pieces.append(gap); new_pos += len(gap)
        line_end = old.index(b"\n", start) + 1
        edits.append({"index": number, "declaration": "AMW.Cert.PC9QB6MData." + name,
                      "original_line_number_1based": old.count(b"\n", 0, start)+1,
                      "original_line_including_terminator_utf8": old[start:line_end].decode(),
                      "old_start_byte": start, "old_end_byte_exclusive": end,
                      "new_start_byte": new_pos, "new_end_byte_exclusive": new_pos+len(replacement),
                      "old_utf8": before.decode(), "replacement_utf8": replacement.decode(), "byte_delta": 14})
        pieces.append(replacement); new_pos += len(replacement); old_pos = end
    gap = old[old_pos:]
    gaps.append({"old_start_byte": old_pos, "old_end_byte_exclusive": len(old),
                 "new_start_byte": new_pos, "new_end_byte_exclusive": new_pos+len(gap), "bytes": len(gap), "sha256": sha(gap)})
    pieces.append(gap)
    new = b"".join(pieces)
    require(len(new) == 1829382 and len(new)-len(old) == 140, "Unexpected source byte delta")
    reverse, new_pos = [], 0
    for edit in edits:
        start, end = edit["new_start_byte"], edit["new_end_byte_exclusive"]
        require(new[start:end] == edit["replacement_utf8"].encode(), "Forward projection failed")
        reverse.extend((new[new_pos:start], edit["old_utf8"].encode())); new_pos = end
    reverse.append(new[new_pos:])
    restored = b"".join(reverse)
    require(restored == old, "Reverse projection failed")
    for gap in gaps:
        require(old[gap["old_start_byte"]:gap["old_end_byte_exclusive"]] == new[gap["new_start_byte"]:gap["new_end_byte_exclusive"]], "Unchanged span altered")
    require(old.count(b"\r\n") == new.count(b"\r\n") == 221 and old.count(b"\r") == new.count(b"\r") == 221, "CRLF normalization occurred")
    require(new.endswith(b"\n") and not new.endswith(b"\n\n"), "Single final LF changed")
    require(not re.search(rb"(?m)^#print axioms ", new), "Deleted diagnostics reintroduced")
    for name in PREVIOUS_NAMES + NAMES:
        require(len(re.findall(rb"(?m)^noncomputable def " + name.encode() + rb"(?=[ \t(])", new)) == 1, "Explicit modifier missing: " + name)
    invariant_patterns = {"48_root_theorem_lines": rb"(?m)^theorem rc[0-9]+ :[^\r\n]*",
                          "135_packed_WL_numeral_lines": rb"(?m)^def WL[0-9]+_[0-9]+ :[^\r\n]*zfNat64[^\r\n]*",
                          "three_public_theorem_declaration_lines": rb"(?m)^theorem candidate_[^\r\n]*"}
    invariants = {}
    for label, pattern in invariant_patterns.items():
        a, b = re.findall(pattern, old), re.findall(pattern, new)
        require(a == b, "Invariant source line altered: " + label)
        invariants[label] = {"count": len(a), "old_equals_new": True, "ordered_lines_sha256": sha(b"\n".join(a))}
    require([v["count"] for v in invariants.values()] == [48, 135, 3], "Invariant line count mismatch")
    for p, row in zip(paths, inputs):
        require(p.stat().st_size == row["bytes"] and sha(p.read_bytes()) == row["sha256"], "Frozen input changed during derivation")
    edits_packet = {"schema": "w9a2-v7-to-v8-exact-byte-edits-v1", "offset_convention": "Zero-based raw UTF8 byte offsets; exclusive end", "edits": edits}
    projection = {"schema": "w9a2-v8-static-projection-v1", "scope": "Static source derivation only; no resource compiler gate or mathematical verification executed",
                  "old_source": {"path": OLD.relative_to(ROOT).as_posix(), "bytes": len(old), "sha256": sha(old)},
                  "new_source": {"path": "Solution.lean", "bytes": len(new), "sha256": sha(new)},
                  "edit_count": 10, "byte_delta": 140, "new_explicit_noncomputable_definitions": list(NAMES),
                  "prior_v7_eight_noncomputable_modifiers_retained": True, "all_fifteen_axiom_prints_remain_absent": True,
                  "forward_exact": True, "reverse_exact": True, "reverse_sha256": sha(restored),
                  "all_other_bytes_identical": True, "unchanged_spans": gaps, "invariants": invariants,
                  "crlf_count": 221, "single_final_LF_preserved": True, "frozen_inputs_before_after_identical": True, "frozen_inputs": inputs,
                  "candidate_compiler_runs": 0, "exporter_runs": 0, "kernel_runs": 0, "solver_runs": 0,
                  "new_source_ordinary_passed": False, "new_source_C_ilean_resource_gate_passed": False,
                  "new_source_kernel_passed": False, "new_source_official_acceptance": False, "counter_modified": False}
    diff = "".join(difflib.unified_diff(old.decode().splitlines(keepends=True), new.decode().splitlines(keepends=True),
                                      fromfile="draft-v7/Solution.lean", tofile="draft-v8/Solution.lean", n=0))
    readme = ("Static v8 derivation from frozen v7 dae01f, authorized by root after source/SDK resource diagnosis.\n"
              "Only ten existing definitions PTT_0 through PTT_7, PTT and PT gain explicit noncomputable modifiers: +140 raw UTF8 bytes.\n"
              "All previous v7 changes, numerical data, every proof body,48 quantitative root checks, attribution and other source bytes are retained.\n"
              "PTT_i -> PTT -> PT is the full native caller closure found in the current source. Other occurrences are theorem terms/types.\n"
              "The macro decoder remains executable and unchanged. Kernel definitions remain transparent; no native oracle or new axiom is introduced.\n"
              "v7 and the original five frozen modules are unchanged.221 CRLF and one final LF are preserved.\n"
              "edits.json and projection.json record exact offsets, original lines, forward and reverse raw-byte identity.\n"
              "No compiler/exporter/kernel/solver/resource test is run. New source validation and official acceptance remain false.\n"
              "Runtime benefit and sufficient peak-memory reduction are unmeasured. A resource gate requires separate root authorization.\n")
    write_new("Solution.lean", new)
    write_new("edits.json", json_bytes(edits_packet))
    write_new("projection.json", json_bytes(projection))
    write_new("exact-source-diff.patch", diff.encode())
    write_new("README.txt", readme.encode())
    files = []
    for name in ("Solution.lean", "derive_v8.py", "edits.json", "projection.json", "exact-source-diff.patch", "README.txt"):
        data = (HERE / name).read_bytes(); files.append({"path": name, "bytes": len(data), "sha256": sha(data)})
    manifest = json_bytes({"schema": "w9a2-static-draft-v8-files-v1", "files": files, "proof_execution_count": 0, "new_source_verified": False})
    write_new("files.json", manifest)
    print(json.dumps({"source_bytes": len(new), "source_sha256": sha(new), "manifest_sha256": sha(manifest),
                      "edits": len(edits), "byte_delta": 140, "reverse_exact": True, "proof_execution_count": 0}))


if __name__ == "__main__":
    main()
