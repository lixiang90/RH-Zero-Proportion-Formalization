"""Independently check exact arithmetic, provenance, and reproducible packaging.

All generator writes are captured in memory. This review does not compile Lean,
replace proof artifacts, or establish website acceptance.
"""
from pathlib import Path
from fractions import Fraction as Q
import argparse
import contextlib
import hashlib
import importlib
import io
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
EXPECTED_SOURCE_HASH = "153e1ebfa23b5ef307dc39e36ee712d6f14d840b3b1fa5ff70b82e9dbc8dd244"
EXPECTED_K = Q(3338957652820594373879991756052499665323,
               4957023073704306225950000000000000000000)
EXPECTED_PREVIOUS = Q(834739413205148593469931805501689594457,
                     1239255769294131601825000000000000000000)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def regenerate_in_memory():
    memory, writes = {}, []
    original = {name: getattr(Path, name) for name in
                ("read_bytes", "read_text", "write_bytes", "write_text")}

    def key(path):
        return str(path.resolve())

    def read_bytes(path):
        return memory[key(path)] if key(path) in memory else original["read_bytes"](path)

    def read_text(path, *args, **kwargs):
        if key(path) not in memory:
            return original["read_text"](path, *args, **kwargs)
        encoding = kwargs.get("encoding") or (args[0] if args else "utf8")
        return memory[key(path)].decode(encoding)

    def write_bytes(path, raw):
        memory[key(path)] = raw
        writes.append(key(path))
        return len(raw)

    def write_text(path, text, encoding=None, errors=None, newline=None):
        assert newline in (None, "\n")
        memory[key(path)] = text.encode(encoding or "utf8", errors or "strict")
        writes.append(key(path))
        return len(text)

    try:
        Path.read_bytes, Path.read_text = read_bytes, read_text
        Path.write_bytes, Path.write_text = write_bytes, write_text
        for name in ("extract_record_20261015", "final_record_20261015", "bundle_record_20261015"):
            with contextlib.redirect_stdout(io.StringIO()):
                importlib.import_module(name).main()
    finally:
        for name, method in original.items():
            setattr(Path, name, method)
    outputs = []
    for value in dict.fromkeys(writes):
        path = Path(value)
        raw = memory[value]
        same = raw == path.read_bytes()
        outputs.append({"path": path.relative_to(ROOT).as_posix(), "bytes": len(raw),
                        "sha256": sha(raw), "generator_reproduces_disk_bytes": same})
    assert len(outputs) == 7 and all(row["generator_reproduces_disk_bytes"] for row in outputs)
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default=str(ROOT / "verification/gram-defect-20261015/packaging-review.json"))
    args = parser.parse_args()
    assert __debug__, "Run with assertions enabled"
    names = ["Core", "SharpWindow", "RefinedCounting", "Final"]
    paths = [ROOT / "GramDefect20261015" / (name + ".lean") for name in names]
    paths += [ROOT / "GramDefect20261015.lean",
        ROOT / "formal/upstream/ajp88-reweighted-nine-point.lean",
        ROOT / "docs/alternating-window-refinement-20261015.md"]
    paths += [ROOT / "scripts" / (name + ".py") for name in
        ("extract_record_20261015", "final_record_20261015", "bundle_record_20261015",
         "bundle_gram_defect_solution")]
    paths += [ROOT / "submission/gram-defect-20261015" / name for name in
        ("README.md", "submission-fields.json", "proof/Solution.lean", "manifest.json")]
    before = {path.relative_to(ROOT).as_posix(): sha(path.read_bytes()) for path in paths}
    assert before["formal/upstream/ajp88-reweighted-nine-point.lean"] == EXPECTED_SOURCE_HASH
    outputs = regenerate_in_memory()
    score = importlib.import_module("final_record_20261015")
    assert score.H == Q(6721684105641188747759983512104999330646, 10**40)
    assert score.C == Q(859538525913875481, 10**20)
    assert score.B == Q(437688000000, 10**14)
    assert score.PREVIOUS == EXPECTED_PREVIOUS and score.K == EXPECTED_K
    assert score.K == (score.H-score.B)/(1-score.C) > score.PREVIOUS
    package = ROOT / "submission/gram-defect-20261015"
    fields = json.loads((package / "submission-fields.json").read_text(encoding="utf8"))
    manifest = json.loads((package / "manifest.json").read_text(encoding="utf8"))
    assert fields["score"] == {"numerator": str(EXPECTED_K.numerator),
                               "denominator": str(EXPECTED_K.denominator)}
    assert fields["summary"] in (package / "README.md").read_text(encoding="utf8")
    raw = (package / "proof/Solution.lean").read_bytes()
    assert len(raw) == manifest["source_bytes"] <= manifest["source_size_limit"] == 2_000_000
    assert sha(raw) == manifest["source_sha256"]
    assert manifest["numerator"] == str(EXPECTED_K.numerator)
    assert manifest["denominator"] == str(EXPECTED_K.denominator)
    assert not fields["submitted"] and not fields["official_website_acceptance"]
    from bundle_gram_defect_solution import code_mask, remaining_sections, strip_imports
    code = code_mask(raw.decode("utf8"))
    assert not re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", code)
    assert not re.search(r"^\s*(?:def|abbrev|opaque)\s+(?:candidateKappa|currentRecordKappa)\b", code, re.M)
    for name in ("candidate_strict_improvement", "candidate_critical_line_bound",
                 "candidate_critical_line_bound_cumulative"):
        assert len(re.findall(r"^theorem " + name + r"\s*:", code, re.M)) == 1
    assert remaining_sections(raw.decode("utf8")) == 0
    _, imports = strip_imports(raw.decode("utf8"))
    assert sorted(imports) == manifest["imports"]
    assert all(not name.startswith("GramDefect") for name in imports)
    for doc in (ROOT / "docs/alternating-window-refinement-20261015.md", package / "README.md"):
        text = doc.read_text(encoding="utf8")
        assert str(EXPECTED_K.numerator) in text and str(EXPECTED_K.denominator) in text
        assert "859538525913875481" in text and "4.71819935420" in text
    after = {path.relative_to(ROOT).as_posix(): sha(path.read_bytes()) for path in paths}
    assert before == after
    receipt = {"review_kind": "independent_exact_arithmetic_provenance_and_in_memory_packaging",
        "passed": True, "input_sha256": before,
        "review_script_sha256": sha(Path(__file__).read_bytes()),
        "generator_outputs": outputs, "frozen_inputs_unchanged": True,
        "exact_ratio": str(EXPECTED_K), "reference_ratio": str(EXPECTED_PREVIOUS),
        "exact_gain": str(EXPECTED_K-EXPECTED_PREVIOUS),
        "submission_bytes": len(raw), "submission_sha256": sha(raw),
        "three_required_roots_unique": True, "trusted_score_constants_not_redefined": True,
        "numerical_docs_and_fields_consistent": True,
        "claim_scope": "Static provenance, exact arithmetic and byte assembly only; "
            "this receipt does not establish Lean, independent-kernel, Comparator, "
            "resource-limit or website acceptance."}
    encoded = json.dumps(receipt, indent=2) + "\n"
    if args.output == "-":
        print(encoded, end="")
    else:
        destination = Path(args.output)
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(encoded, encoding="utf8", newline="\n")
        print(json.dumps({"passed": True, "output": str(destination)}))


if __name__ == "__main__":
    main()
