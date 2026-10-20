"""Static byte derivation only: eight modifiers and fifteen diagnostic deletions."""
from pathlib import Path
import difflib
import hashlib
import json
import os
import re


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OLD = ROOT / "research-goal-20261020-w9a2-delivery/draft-v6/Solution.lean"
OLD_SHA = "a517df6aebde6d136f8b83e06c8be10b3413b8430390f52bd47f04e06f0dce26"
NAMES = ("mcheckP", "mleafP", "leafStep", "node", "walkC", "walk", "walkCut", "walkCutR")
OUTPUTS = ("Solution.lean", "edits.json", "projection.json", "exact-source-diff.patch", "README.txt", "files.json")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write_new(name: str, data: bytes) -> None:
    with (HERE / name).open("xb") as stream:
        stream.write(data)
        stream.flush()
        os.fsync(stream.fileno())


def json_bytes(value) -> bytes:
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")


def main() -> None:
    if any((HERE / name).exists() for name in OUTPUTS):
        raise RuntimeError("Exclusive output already exists; no overwrite permitted")
    old = OLD.read_bytes()
    if len(old) != 1830052 or sha(old) != OLD_SHA:
        raise RuntimeError("Frozen v6 byte identity mismatch")
    old.decode("utf-8")
    immutable_paths = [OLD, OLD.parent / "files.json"] + [
        OLD.parent / "frozen-inputs/StructuralW9A220261020" / (name + ".lean")
        for name in ("Core", "Graph", "Localization", "Counting", "Final")
    ]
    inputs = [{"path": p.relative_to(ROOT).as_posix(), "bytes": p.stat().st_size,
               "sha256": sha(p.read_bytes())} for p in immutable_paths]
    edits = []
    for name in NAMES:
        matches = list(re.finditer(rb"(?m)^def " + name.encode() + rb"(?=[ \t(])", old))
        if len(matches) != 1:
            raise RuntimeError(f"Expected exactly one unmodified declaration: {name}")
        match = matches[0]
        edits.append({"kind": "explicit_noncomputable_modifier", "declaration": "AMW.Cert.PC9QB6M." + name,
                      "start": match.start(), "end": match.end(),
                      "old": match.group(), "new": b"noncomputable " + match.group()})
    prints = list(re.finditer(rb"(?m)^#print axioms [^\r\n]*(?:\r\n|\n|$)", old))
    if len(prints) != 15 or sum(len(m.group()) for m in prints) != 922:
        raise RuntimeError("Expected exactly fifteen full diagnostic lines totaling 922 bytes")
    for match in prints:
        if not match.group().endswith(b"\n"):
            raise RuntimeError("Diagnostic line lacks its original LF terminator")
        edits.append({"kind": "remove_standalone_axiom_print", "start": match.start(), "end": match.end(),
                      "old": match.group(), "new": b""})
    edits.sort(key=lambda e: e["start"])
    pieces, cursor, size, records, unchanged = [], 0, 0, [], []
    for index, edit in enumerate(edits, 1):
        if edit["start"] < cursor or old[edit["start"]:edit["end"]] != edit["old"]:
            raise RuntimeError("Overlapping or inexact edit")
        gap = old[cursor:edit["start"]]
        unchanged.append({"old_start_byte": cursor, "old_end_byte_exclusive": edit["start"],
                          "new_start_byte": size, "new_end_byte_exclusive": size + len(gap),
                          "bytes": len(gap), "sha256": sha(gap)})
        pieces.append(gap)
        size += len(gap)
        line_end = old.find(b"\n", edit["start"])
        line_end = len(old) if line_end < 0 else line_end + 1
        original_line = old[edit["start"]:line_end]
        record = {"index": index, "kind": edit["kind"],
                  "original_line_number_1based": old.count(b"\n", 0, edit["start"]) + 1,
                  "original_line_including_terminator_utf8": original_line.decode("utf-8"),
                  "old_start_byte": edit["start"], "old_end_byte_exclusive": edit["end"],
                  "new_start_byte": size, "new_end_byte_exclusive": size + len(edit["new"]),
                  "old_utf8": edit["old"].decode("utf-8"), "replacement_utf8": edit["new"].decode("utf-8"),
                  "byte_delta": len(edit["new"]) - len(edit["old"])}
        if "declaration" in edit:
            record["declaration"] = edit["declaration"]
        records.append(record)
        pieces.append(edit["new"])
        size += len(edit["new"])
        cursor = edit["end"]
    gap = old[cursor:]
    unchanged.append({"old_start_byte": cursor, "old_end_byte_exclusive": len(old),
                      "new_start_byte": size, "new_end_byte_exclusive": size + len(gap),
                      "bytes": len(gap), "sha256": sha(gap)})
    pieces.append(gap)
    new = b"".join(pieces)
    if len(new) != 1829242 or len(new) - len(old) != 112 - 922:
        raise RuntimeError("Expected exact byte delta -810")
    reverse, new_cursor = [], 0
    for record in records:
        start, end = record["new_start_byte"], record["new_end_byte_exclusive"]
        replacement = record["replacement_utf8"].encode("utf-8")
        if new[start:end] != replacement:
            raise RuntimeError("Forward span identity failure")
        reverse.extend((new[new_cursor:start], record["old_utf8"].encode("utf-8")))
        new_cursor = end
    reverse.append(new[new_cursor:])
    restored = b"".join(reverse)
    if restored != old:
        raise RuntimeError("Reverse projection is not exact v6 bytes")
    for row in unchanged:
        old_gap = old[row["old_start_byte"]:row["old_end_byte_exclusive"]]
        new_gap = new[row["new_start_byte"]:row["new_end_byte_exclusive"]]
        if old_gap != new_gap:
            raise RuntimeError("Unchanged segment mismatch")
    if new.count(b"\r\n") != 221 or new.count(b"\r") != 221:
        raise RuntimeError("Original 221 CRLF sequences changed")
    if new.endswith(b"\n\n") or not new.endswith(b"\n") or re.search(rb"(?m)^#print axioms ", new):
        raise RuntimeError("Trailing LF or diagnostic removal mismatch")
    for name in NAMES:
        if len(re.findall(rb"(?m)^noncomputable def " + name.encode() + rb"(?=[ \t(])", new)) != 1:
            raise RuntimeError("Explicit modifier identity failure")
    invariant_patterns = {
        "48_quantitative_root_theorem_lines": rb"(?m)^theorem rc[0-9]+ :[^\r\n]*",
        "135_packed_numeral_definition_lines": rb"(?m)^def WL[0-9]+_[0-9]+ :[^\r\n]*",
        "three_public_theorem_declaration_lines": rb"(?m)^theorem candidate_[^\r\n]*",
    }
    invariants = {}
    for label, pattern in invariant_patterns.items():
        a, b = re.findall(pattern, old), re.findall(pattern, new)
        if a != b:
            raise RuntimeError("Invariant line changed: " + label)
        invariants[label] = {"count": len(a), "old_equals_new": True, "ordered_lines_sha256": sha(b"\n".join(a))}
    if [row["count"] for row in invariants.values()] != [48, 135, 3]:
        raise RuntimeError("Invariant count mismatch")
    for row, p in zip(inputs, immutable_paths):
        if p.stat().st_size != row["bytes"] or sha(p.read_bytes()) != row["sha256"]:
            raise RuntimeError("Frozen input changed during derivation")
    edit_packet = {"schema": "w9a2-v6-to-v7-exact-byte-edits-v1", "offset_convention": "zero-based UTF-8 byte offsets, exclusive end",
                   "edits": records}
    projection = {"schema": "w9a2-static-v7-projection-v1", "scope": "Static byte derivation only; no compiler/exporter/kernel execution",
                  "old_source": {"path": OLD.relative_to(ROOT).as_posix(), "bytes": len(old), "sha256": sha(old)},
                  "new_source": {"path": "Solution.lean", "bytes": len(new), "sha256": sha(new)},
                  "modifier_insertions": 8, "modifier_bytes_added": 112, "diagnostic_lines_removed": 15,
                  "diagnostic_bytes_removed": 922, "total_byte_delta": -810,
                  "forward_exact": True, "reverse_exact": True, "reverse_sha256": sha(restored),
                  "all_other_bytes_identical": True, "unchanged_segments": unchanged,
                  "source_crlf_count_old": old.count(b"\r\n"), "source_crlf_count_new": new.count(b"\r\n"),
                  "single_final_lf_preserved": True, "invariants": invariants,
                  "frozen_inputs_before_after_identical": True, "frozen_inputs": inputs,
                  "candidate_compiler_runs": 0, "exporter_runs": 0, "kernel_runs": 0,
                  "new_source_ordinary_pass": False, "new_source_independent_kernel_pass": False,
                  "new_source_official_acceptance": False, "counter_modified": False}
    diff = "".join(difflib.unified_diff(old.decode("utf-8").splitlines(keepends=True),
                                      new.decode("utf-8").splitlines(keepends=True),
                                      fromfile="draft-v6/Solution.lean", tofile="draft-v7/Solution.lean", n=0))
    readme = ("Static v7 derivation from frozen a517 draft-v6, authorized by root.\n"
              "Exactly eight explicit noncomputable modifiers and deletion of all fifteen standalone #print axioms commands.\n"
              "All remaining bytes, numerical certificates, 48 root checks, declarations, theorem bodies and attribution are preserved.\n"
              "Original v6 and its five frozen modules are unchanged. CRLF count remains 221; the single final LF is retained.\n"
              "edits.json records each original line, replacement and old/new byte offset. projection.json records exact forward/reverse byte identity.\n"
              "This is source preparation only: zero Lean/compiler/exporter/kernel/solver runs; no local verification or official acceptance claimed.\n"
              "Code generation suppression leaves kernel definitions transparent. Macro decoder digit64/decode64 remains executable and unchanged.\n"
              "Deleted prints are diagnostics only. The official Comparator/axiom and kernel gates remain necessary.\n")
    write_new("Solution.lean", new)
    write_new("edits.json", json_bytes(edit_packet))
    write_new("projection.json", json_bytes(projection))
    write_new("exact-source-diff.patch", diff.encode("utf-8"))
    write_new("README.txt", readme.encode("utf-8"))
    files = []
    for name in ("Solution.lean", "derive_v7.py", "edits.json", "projection.json", "exact-source-diff.patch", "README.txt"):
        data = (HERE / name).read_bytes()
        files.append({"path": name, "bytes": len(data), "sha256": sha(data)})
    write_new("files.json", json_bytes({"schema": "w9a2-static-draft-v7-files-v1", "files": files,
                                        "proof_execution_count": 0, "new_source_verified": False}))
    print(json.dumps({"source_bytes": len(new), "source_sha256": sha(new),
                      "manifest_sha256": sha((HERE / "files.json").read_bytes()),
                      "edits": len(records), "byte_delta": len(new) - len(old),
                      "forward_reverse_exact": True, "proof_execution_count": 0}))


if __name__ == "__main__":
    main()
