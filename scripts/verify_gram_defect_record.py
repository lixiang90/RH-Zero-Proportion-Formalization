"""Check the exact record arithmetic and freshly audit all headline axioms.

Run after `lake --no-cache build +GramDefectRecord:olean`. This uses ordinary
Lean; independent nanoda receipts are archived separately in verification.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import subprocess
from fractions import Fraction as Q

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ROOTS = ["GramDefectRecord." + n for n in (
    "exact_formula", "strict_improvement", "simple_dyadic", "simple_cumulative",
    "distinct_dyadic", "distinct_cumulative")]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def strip_comments(text):
    # Lean block comments are nested. Keep all non-comment bytes for the scan.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1; i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1; i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i]); i += 1
    assert depth == 0, "Unbalanced block comment"
    return "".join(out)

def main():
    if not __debug__:
        raise SystemExit("Assertions must remain enabled")
    sources = sorted((ROOT / "GramDefectRecord").glob("*.lean")) + [ROOT / "GramDefectRecord.lean"]
    before = {str(p.relative_to(ROOT)): sha(p) for p in sources}
    for p in sources:
        code = strip_comments(p.read_text(encoding="utf8"))
        assert not re.search(r"(?<![\w])(?:sorry|admit|native_decide|unsafe|axiom)(?![\w])", code), p
    h = Q(672168410564118874775945444401, 10**30)
    c = Q(85638285989, 10**13)
    b = Q(436674, 10**8)
    k = Q(39282451209654051457408555553, 58319774788300000000000000000)
    old = Q(667801670564118872522651, 991436171500000000000000)
    assert k == (h-b)/(1-c) and k > old
    scratch = ROOT / "tmp/verification/gram-defect-20261014"
    scratch.mkdir(parents=True, exist_ok=True)
    audit = scratch / "Audit.lean"
    audit.write_text("import GramDefectRecord\n" + "\n".join("#print axioms " + n for n in ROOTS) + "\n", encoding="utf8", newline="\n")
    command = ["lake", "--no-cache", "env", "lean", str(audit)]
    proc = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, encoding="utf8", errors="replace")
    text = proc.stdout + proc.stderr
    blocks = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", text)
    observed = {n.strip() for block in blocks for n in block.split(",") if n.strip()}
    count = len(blocks) + len(re.findall("does not depend on any axioms", text))
    after = {str(p.relative_to(ROOT)): sha(p) for p in sources}
    passed = proc.returncode == 0 and count == len(ROOTS) and observed <= ALLOWED and before == after
    receipt = {"roots": ROOTS, "source_sha256": before, "inputs_unchanged": before == after,
        "exact_ratio": str(k), "previous_site_ratio": str(old), "strict_gain": str(k-old),
        "command": command, "exit_code": proc.returncode, "observed_axioms": sorted(observed),
        "audited_roots": count, "passed": passed, "official_website_acceptance": False}
    (scratch / "audit.log").write_text(text, encoding="utf8", newline="\n")
    (scratch / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf8", newline="\n")
    print(json.dumps(receipt, indent=2))
    if not passed:
        raise SystemExit(text)

if __name__ == "__main__":
    main()
