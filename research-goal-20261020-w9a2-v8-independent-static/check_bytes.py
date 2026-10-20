"""Independent v7-to-v8 byte projection; no project code is imported."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(__file__).resolve().parent
OLD = ROOT / "research-goal-20261020-w9a2-delivery/draft-v7/Solution.lean"
NEW = ROOT / "research-goal-20261020-w9a2-delivery/draft-v8/Solution.lean"
NAMES = tuple(f"PTT_{i}" for i in range(8)) + ("PTT", "PT")
PRIOR = ("mcheckP", "mleafP", "leafStep", "node", "walkC", "walk", "walkCut", "walkCutR")
PREFIX = b"noncomputable "

def sha(b):
    return hashlib.sha256(b).hexdigest()

def pin(p):
    b = p.read_bytes()
    return {"path": p.relative_to(ROOT).as_posix(), "bytes": len(b), "sha256": sha(b)}

package_manifest = NEW.parent / "files.json"
package = json.loads(package_manifest.read_bytes())
assert sha(package_manifest.read_bytes()) == "7f449697314ee04088f1874a6cfdd609c02bb322995feb1197406133ded2a776"
assert len(package["files"]) == 6
inputs = [OLD, package_manifest]
for row in package["files"]:
    p = NEW.parent / row["path"]
    actual = pin(p)
    assert actual["bytes"] == row["bytes"] and actual["sha256"] == row["sha256"], row
    inputs.append(p)
before = [pin(p) for p in inputs]
old, new = OLD.read_bytes(), NEW.read_bytes()
assert len(old) == 1829242 and sha(old) == "dae01f6844642d7f9ee8180616c1f57aefc18ab8616bc8a4a46a14bf8e9fefc6"
assert len(new) == 1829382 and sha(new) == "5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b"

edits = []
for name in NAMES:
    matches = list(re.finditer(rb"(?m)^def " + name.encode() + rb"\b", old))
    assert len(matches) == 1, (name, len(matches))
    m = matches[0]
    edits.append({"name": name, "old_offset": m.start(), "old_line": old[:m.start()].count(b"\n") + 1})
edits.sort(key=lambda row: row["old_offset"])
parts, cursor = [], 0
for i, row in enumerate(edits):
    at = row["old_offset"]
    parts.extend((old[cursor:at], PREFIX))
    cursor = at
    row.update({"new_offset": at + i * len(PREFIX), "new_line": row["old_line"], "inserted_bytes": len(PREFIX)})
parts.append(old[cursor:])
assert b"".join(parts) == new, "Unexpected byte change outside the ten authorized prefixes"

reverse = new
for row in reversed(edits):
    at = row["new_offset"]
    assert reverse[at:at + len(PREFIX)] == PREFIX
    reverse = reverse[:at] + reverse[at + len(PREFIX):]
assert reverse == old
for name in NAMES:
    assert len(re.findall(rb"(?m)^noncomputable def " + name.encode() + rb"\b", new)) == 1
    assert not re.search(rb"(?m)^def " + name.encode() + rb"\b", new)
for name in PRIOR:
    needle = rb"(?m)^noncomputable def " + name.encode() + rb"\b"
    assert len(re.findall(needle, old)) == len(re.findall(needle, new)) == 1
assert not re.search(rb"(?m)^#print axioms ", old)
assert not re.search(rb"(?m)^#print axioms ", new)
assert old.count(b"\r\n") == new.count(b"\r\n") == 221
assert old.count(b"\r") == new.count(b"\r") == 221
assert old.count(b"\n") == new.count(b"\n")
assert old.endswith(b"\n") and new.endswith(b"\n")
rc_pattern = rb"(?m)^theorem rc([0-9]+)\b[^\r\n]*"
old_rc = [(m.group(1), m.group(0)) for m in re.finditer(rc_pattern, old)]
new_rc = [(m.group(1), m.group(0)) for m in re.finditer(rc_pattern, new)]
assert old_rc == new_rc and [name for name, _ in old_rc] == [str(i).encode() for i in range(48)]
after = [pin(p) for p in inputs]
assert before == after
result = {
    "schema": "w9a2-v8-independent-byte-review-v1",
    "result": "PASS_STATIC_BYTE_PROJECTION",
    "old_sha256": sha(old), "old_bytes": len(old),
    "new_sha256": sha(new), "new_bytes": len(new),
    "exact_edit_count": 10, "inserted_bytes": 140, "deleted_bytes": 0,
    "edits": edits, "all_other_bytes_preserved": True,
    "reverse_projection_equals_v7": True, "prior_eight_noncomputable_markers_preserved": True,
    "zero_print_axioms_commands_preserved": True, "rc0_through_rc47_lines_preserved": True,
    "crlf_count": 221, "bare_cr_count": 0, "lf_count": new.count(b"\n"), "final_lf": True,
    "package_manifest_rows_checked": 6, "input_pins": after, "input_hashes_unchanged": True,
    "proof_execution_count": 0, "candidate_source_mutation_count": 0,
    "compiled_exported_or_kernel_checked": False, "performance_improvement_measured": False,
    "official_acceptance": False,
    "scope": "Independent raw-byte audit only. Exact labels PTT_0..7/PTT/PT have unique def anchors. Every other source byte, including proofs/data/public roots, is preserved. Neither package derivation script was imported or executed. Consumer closure and codegen semantics remain the separate formal resource review."
}
(OUT / "byte-review.json").write_text(json.dumps(result, ensure_ascii=True, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"result": result["result"], "source_bytes": len(new), "source_sha256": sha(new), "edits": len(edits), "proof_runs": 0}))
