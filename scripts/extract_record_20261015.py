"""Extract the accepted 15 October record without its fixed-score wrapper.

The archived upstream bytes and every license notice are preserved. The
new library is independent of the historical GramDefectRecord library,
whose inherited declaration names overlap with this source.
"""
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from bundle_gram_defect_solution import remaining_sections


def main():
    source = ROOT / "formal/upstream/ajp88-reweighted-nine-point.lean"
    raw = source.read_bytes()
    expected_sha = "153e1ebfa23b5ef307dc39e36ee712d6f14d840b3b1fa5ff70b82e9dbc8dd244"
    if hashlib.sha256(raw).hexdigest() != expected_sha:
        raise ValueError("Archived accepted source differs from the fixed upstream bytes")
    text = raw.decode("utf8").replace("\r\n", "\n")
    trailer = text[text.index("/-\nADDITIONAL THIRD-PARTY NOTICES AND LICENSE TEXTS"):]
    marker = "-- SWAP final instantiation: n, the certificate's W / W_adm / W_B / cert_AM, c, B, κ"
    body = text[:text.index(marker)]
    assert body.count("import ChallengeDeps\n") == 1
    assert body.count("import ChallengeDeps.CandidateSpec\n") == 1
    body = body.replace("import ChallengeDeps\n", "import Zeta23.FinalMult\n")
    body = body.replace("import ChallengeDeps.CandidateSpec\n", "")
    # Exact replay of every inherited leaf and root-cover condition permits
    # this stronger integer floor. The ordinary Lean `decide` proofs remain
    # unchanged and must be rebuilt, so the Python audit is not a proof oracle.
    old_floor, new_floor = "859538456469471854", "859538525913875481"
    assert body.count(old_floor) == 2
    body = body.replace(old_floor, new_floor)
    closed = remaining_sections(body)
    header = """/-
Copyright (c) 2026 Li Xiang (lixiang90), modifications. Apache-2.0.
Modified 2026-10-15: modular extraction of the accepted ajp88 reweighted
nine-point proof at e08fce410ba008ff5c5a03215d9b6bfb3ab91200.
Only the challenge imports and final fixed-score composition are removed.
The local floor is raised to 859538525913875481/10^20; all existing
ordinary Lean checks are rebuilt. The window, checker, certificate tree,
weights, pressures, counting chain, and source/license notices remain.
New improvements are proved in separate modules.
-/
"""
    output = ROOT / "GramDefect20261015/Core.lean"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(header + body + "end\n" * closed + trailer, encoding="utf8", newline="\n")
    counting = (ROOT / "GramDefectRecord/RefinedCounting.lean").read_text(encoding="utf8")
    counting = counting.replace("GramDefectRecord", "GramDefect20261015")
    counting = counting.replace("Modified from the counting bridge by R. Arun Chandru in the accepted\nmaster-of-puppets4 record, commit 65c71d512f51df92bec4a3d1edb6a795fc1cac63.",
        "Reused 2026-10-15 with the accepted ajp88 nine-point certificate.\nThe generic counting argument is unchanged from the 2026-10-14 module,\nbased on R. Arun Chandru's master-of-puppets4 counting bridge.")
    (output.parent / "RefinedCounting.lean").write_text(counting, encoding="utf8", newline="\n")
    report = {
        "url": "https://raw.githubusercontent.com/josusanmartin/riemann/e08fce410ba008ff5c5a03215d9b6bfb3ab91200/submissions/ajp88-reweighted-nine-point/proof/Solution.lean",
        "upstream_commit": "e08fce410ba008ff5c5a03215d9b6bfb3ab91200",
        "upstream_sha256": hashlib.sha256(raw).hexdigest(),
        "upstream_bytes": len(raw),
        "core_sha256": hashlib.sha256(output.read_bytes()).hexdigest(),
        "local_floor_replacement": {"old_numerator": old_floor, "new_numerator": new_floor,
                                    "denominator": "100000000000000000000", "occurrences": 2},
        "implicit_sections_closed": closed,
        "license_trailer_preserved": output.read_text(encoding="utf8").endswith(trailer),
    }
    target = ROOT / "verification/gram-defect-20261015"
    target.mkdir(parents=True, exist_ok=True)
    (target / "upstream-extraction.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf8", newline="\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
