"""Read frozen bytes only; construct the authorized projection in memory.

This does not import project Python, create a Lean source, or run any compiler.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(__file__).resolve().parent
OLD = ROOT / "submission/w9a2-weighted-potential-20261020-prepared-v6/proof/Solution.lean"
NEW = ROOT / "research-goal-20261020-w9a2-delivery/draft-v7/Solution.lean"
PACKAGE = NEW.parent
EXPECTED_OLD = "a517df6aebde6d136f8b83e06c8be10b3413b8430390f52bd47f04e06f0dce26"
EXPECTED_NEW = "dae01f6844642d7f9ee8180616c1f57aefc18ab8616bc8a4a46a14bf8e9fefc6"
DEFS = ("mcheckP", "mleafP", "leafStep", "node", "walkC", "walk", "walkCut", "walkCutR")
PRINTS = (
    "StructuralW9A220261020.Counting.sum_range_coboundary_lower",
    "StructuralW9A220261020.Counting.summed_of_state",
    "StructuralW9A220261020.Counting.actual_defect_estimate_effective",
    "StructuralW9A220261020.Counting.actual_dyadic_of_summed",
    "StructuralW9A220261020.Counting.actual_cumulative_of_summed",
    "StructuralW9A220261020.Localization.located_state",
    "StructuralW9A220261020.Graph.edge_from_locations",
    "StructuralW9A220261020.Graph.edge_potential",
    "StructuralW9A220261020.Final.actual_summed",
    "StructuralW9A220261020.Final.strict_improvement",
    "StructuralW9A220261020.Final.actual_dyadic",
    "StructuralW9A220261020.Final.actual_cumulative",
    "candidate_strict_improvement",
    "candidate_critical_line_bound",
    "candidate_critical_line_bound_cumulative",
)

def digest(b):
    return hashlib.sha256(b).hexdigest()

def pin(p):
    b = p.read_bytes()
    return {"path": p.relative_to(ROOT).as_posix(), "bytes": len(b), "sha256": digest(b)}

def shape(b):
    return {"bytes": len(b), "lf": b.count(b"\n"), "crlf": b.count(b"\r\n"),
            "bare_cr": b.count(b"\r") - b.count(b"\r\n"), "final_lf": b.endswith(b"\n")}

inputs = [OLD, NEW, PACKAGE / "files.json"]
manifest = json.loads((PACKAGE / "files.json").read_bytes())
for row in manifest["files"]:
    p = PACKAGE / row["path"]
    actual = pin(p)
    assert actual["bytes"] == row["bytes"] and actual["sha256"] == row["sha256"], row
    inputs.append(p)
inputs = list(dict.fromkeys(inputs))
before = [pin(p) for p in inputs]
old, new = OLD.read_bytes(), NEW.read_bytes()
assert digest(old) == EXPECTED_OLD and len(old) == 1830052
assert digest(new) == EXPECTED_NEW and len(new) == 1829242

edits = []
for name in DEFS:
    matches = list(re.finditer(rb"(?m)^def " + name.encode() + rb"\b", old))
    assert len(matches) == 1, (name, len(matches))
    m = matches[0]
    edits.append({"start": m.start(), "end": m.start(), "before": b"",
                  "after": b"noncomputable ", "kind": "modifier", "name": name})
print_matches = list(re.finditer(rb"(?m)^#print axioms ([^\r\n]+)(\r?\n|$)", old))
assert len(print_matches) == 15
assert tuple(m.group(1).decode("utf-8") for m in print_matches) == PRINTS
for m in print_matches:
    edits.append({"start": m.start(), "end": m.end(), "before": m.group(0),
                  "after": b"", "kind": "diagnostic", "name": m.group(1).decode()})
edits.sort(key=lambda e: (e["start"], e["end"]))
assert len(edits) == 23
assert sum(len(e["after"]) for e in edits) == 112
assert sum(len(e["before"]) for e in edits) == 922

parts, cursor, shift = [], 0, 0
output_edits = []
for e in edits:
    assert e["start"] >= cursor and old[e["start"]:e["end"]] == e["before"]
    parts.extend((old[cursor:e["start"]], e["after"]))
    new_start = e["start"] + shift
    output_edits.append({"kind": e["kind"], "name": e["name"],
                         "old_offset": e["start"], "old_line": old[:e["start"]].count(b"\n") + 1,
                         "new_offset": new_start, "new_line": new[:new_start].count(b"\n") + 1,
                         "removed_bytes": len(e["before"]), "inserted_bytes": len(e["after"])})
    cursor = e["end"]
    shift += len(e["after"]) - len(e["before"])
parts.append(old[cursor:])
assert b"".join(parts) == new, "Unauthorized byte change outside the 23 expected edits"

# Independent reverse operation uses only located new modifier lines and the
# calculated deletion offsets. This must restore every original byte.
back = new
for e, o in reversed(list(zip(edits, output_edits))):
    start = o["new_offset"]
    assert back[start:start + len(e["after"])] == e["after"]
    back = back[:start] + e["before"] + back[start + len(e["after"]):]
assert back == old
assert not re.search(rb"(?m)^#print axioms ", new)
for name in DEFS:
    assert len(re.findall(rb"(?m)^noncomputable def " + name.encode() + rb"\b", new)) == 1
    assert not re.search(rb"(?m)^def " + name.encode() + rb"\b", new)

old_rc = re.findall(rb"(?m)^theorem rc([0-9]+)\b[^\r\n]*", old)
new_rc = re.findall(rb"(?m)^theorem rc([0-9]+)\b[^\r\n]*", new)
assert old_rc == new_rc and old_rc == [str(i).encode() for i in range(48)]
assert shape(old)["crlf"] == shape(new)["crlf"] == 221
assert shape(old)["bare_cr"] == shape(new)["bare_cr"] == 0
assert shape(old)["final_lf"] and shape(new)["final_lf"]
after = [pin(p) for p in inputs]
assert after == before, "Frozen input changed during the audit"

result = {
    "schema": "w9a2-v7-independent-byte-review-v1",
    "result": "PASS_STATIC_BYTE_PROJECTION",
    "old": {"sha256": digest(old), **shape(old)},
    "new": {"sha256": digest(new), **shape(new)},
    "edits": output_edits,
    "exact_authorized_edit_count": 23,
    "all_other_bytes_preserved": True,
    "reverse_projection_equals_old": True,
    "rc0_through_rc47_source_lines_unchanged": True,
    "input_hashes_unchanged": True,
    "input_pins": after,
    "proof_execution_count": 0,
    "new_source_compiled_exported_or_kernel_checked": False,
    "official_acceptance": False,
    "scope": "Frozen source bytes and seven-row package manifest only; no derivation script imported or executed. All other mathematical declarations, proofs, numeric data and the parked dead consumers are preserved by byte identity."
}
(OUT / "byte-review.json").write_text(json.dumps(result, ensure_ascii=True, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"result": result["result"], "new_sha256": digest(new), "bytes": len(new),
                  "edits": len(edits), "input_files": len(after), "proof_execution_count": 0}))
