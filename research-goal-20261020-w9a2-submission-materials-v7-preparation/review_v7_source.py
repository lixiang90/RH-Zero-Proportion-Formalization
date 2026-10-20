"""Independent byte-only review; never invokes Lean, exporters, kernels or network."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
V6 = ROOT / "research-goal-20261020-w9a2-delivery/draft-v6"
V7 = ROOT / "research-goal-20261020-w9a2-delivery/draft-v7"
OLD_SHA = "a517df6aebde6d136f8b83e06c8be10b3413b8430390f52bd47f04e06f0dce26"
NEW_SHA = "dae01f6844642d7f9ee8180616c1f57aefc18ab8616bc8a4a46a14bf8e9fefc6"
MANIFEST_SHA = "08844b98778d5197ad39cd6afe0c796f94e1808f04f17a348f18c8f2bd4efab1"
NAMES = ("mcheckP", "mleafP", "leafStep", "node", "walkC", "walk", "walkCut", "walkCutR")


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def pin(path):
    raw = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "bytes": len(raw), "sha256": sha(raw)}


def write(path, value):
    with path.open("xb") as stream:
        stream.write((json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode())


def main():
    assert __debug__ and not (HERE / "source-review.json").exists()
    assert sha((V7 / "files.json").read_bytes()) == MANIFEST_SHA
    manifest = json.loads((V7 / "files.json").read_bytes())
    inputs = [pin(V6 / "Solution.lean"), pin(V7 / "files.json")]
    for row in manifest["files"]:
        path = (V7 / row["path"]).resolve()
        assert path.is_relative_to(V7.resolve())
        observed = pin(path)
        assert observed["bytes"] == row["bytes"] and observed["sha256"] == row["sha256"]
        inputs.append(observed)
    old = (V6 / "Solution.lean").read_bytes()
    new = (V7 / "Solution.lean").read_bytes()
    assert len(old) == 1830052 and sha(old) == OLD_SHA
    assert len(new) == 1829242 and sha(new) == NEW_SHA
    # Independently derive the allowed transformation from original lines,
    # rather than execute the author generator or rely on its edits.json.
    expected, modifiers, prints = [], [], []
    for number, line in enumerate(old.splitlines(keepends=True), 1):
        if re.fullmatch(rb"#print axioms [^\r\n]+\n", line):
            prints.append({"old_line": number, "bytes": len(line), "sha256": sha(line)})
            continue
        for name in NAMES:
            if re.match(rb"def " + name.encode() + rb"(?=[ (\t])", line):
                modifiers.append({"old_line": number, "name": name})
                line = b"noncomputable " + line
                break
        expected.append(line)
    assert tuple(row["name"] for row in modifiers) == NAMES
    assert len(prints) == 15 and sum(row["bytes"] for row in prints) == 922
    assert b"".join(expected) == new
    assert len(new) - len(old) == 8 * 14 - 922 == -810
    # Independently verify the authored offset map in both directions.
    edits = json.loads((V7 / "edits.json").read_bytes())["edits"]
    assert len(edits) == 23
    reverse, cursor = [], 0
    for edit in edits:
        a, b = edit["new_start_byte"], edit["new_end_byte_exclusive"]
        assert a >= cursor and new[a:b] == edit["replacement_utf8"].encode()
        assert old[edit["old_start_byte"]:edit["old_end_byte_exclusive"]] == edit["old_utf8"].encode()
        reverse.extend((new[cursor:a], edit["old_utf8"].encode()))
        cursor = b
    reverse.append(new[cursor:])
    assert b"".join(reverse) == old
    assert new.count(b"\r\n") == old.count(b"\r\n") == 221
    assert new.count(b"\r") == 221 and new.endswith(b"\n") and not new.endswith(b"\n\n")
    assert not re.search(rb"(?m)^#print axioms ", new)
    for row in inputs:
        assert pin(ROOT / row["path"]) == row
    report = {"schema": "w9a2-v7-independent-static-source-review-v1",
        "scope": "Independent source byte preservation and frozen-input identity only; no mathematical validation of v7",
        "independent_derivation_matches": True, "independent_reverse_projection_matches": True,
        "source": pin(V7 / "Solution.lean"), "old_source": pin(V6 / "Solution.lean"),
        "modifier_insertions": modifiers, "removed_diagnostics": prints,
        "all_other_bytes_preserved": True, "total_byte_delta": -810,
        "attributions_licenses_proof_bodies_data_and_theorem_types_preserved_by_byte_identity": True,
        "v7_local_Lean_passed": False, "v7_export_passed": False, "v7_kernel_passed": False,
        "v7_official_result_observed": False, "proof_compiler_export_kernel_network_calls": 0,
        "inputs": inputs}
    write(HERE / "source-review.json", report)
    write(HERE / "source-review-files.json", {"schema": "w9a2-v7-static-source-review-files-v1",
        "files": [dict(path=p.name, bytes=p.stat().st_size, sha256=sha(p.read_bytes()))
                  for p in (HERE / "review_v7_source.py", HERE / "source-review.json")]})
    print(json.dumps({"review_manifest_sha256": sha((HERE / "source-review-files.json").read_bytes()),
                      "source_sha256": NEW_SHA, "proof_execution_count": 0}))


if __name__ == "__main__":
    main()
