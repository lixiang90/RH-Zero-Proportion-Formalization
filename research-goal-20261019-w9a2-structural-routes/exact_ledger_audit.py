"""Deterministic rational audit only; no kernel calls or optimization."""
from __future__ import annotations
import ast
import hashlib
import json
import re
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HERE = Path(__file__).resolve().parent
SOURCE = ROOT / "research-goal-20261019-w9a2-record/official/proof/Solution.lean"
EXPECTED = "241068ee5abab772ea1aba7533ec33b9140df7dc1728aeb4c61bfb648fe195c7"

raw = SOURCE.read_bytes()
sha = hashlib.sha256(raw).hexdigest()
assert sha == EXPECTED
text = raw.decode("utf-8")
start = text.index("namespace AMW.Cert.PC9QB6M")
part = text[start:]
terms = ast.literal_eval(re.search(r"^def TS : List Term := (.*)$", part, re.M).group(1))
assert len(terms) == 34
a = {(i, j): Q(coef, 10**20) for i, j, coef, _ in terms}
assert len(a) == 34
assert all(coef >= 0 for coef in a.values())

masses = {}
coefficient_checks = []
range_bound = Q(0)
for distance in range(1, 9):
    coeff = [a.get((i, i + distance), Q(0)) for i in range(9 - distance)]
    mass = sum(coeff)
    masses[str(distance)] = str(mass)
    # Compare with canonical ledger a'[0,s] = A_s, all other a' = 0.
    diff = [entry - (mass if i == 0 else 0) for i, entry in enumerate(coeff)]
    assert sum(diff) == 0
    prefix = [sum(diff[: i + 1]) for i in range(len(diff) - 1)]
    assert all(v <= 0 for v in prefix)
    reconstructed = [
        (prefix[i] if i < len(prefix) else 0)
        - (prefix[i - 1] if i > 0 else 0)
        for i in range(len(diff))
    ]
    assert reconstructed == diff
    range_bound += sum(-v for v in prefix)
    coefficient_checks.append({
        "distance": distance,
        "identity": "C_i - C_(i-1) = delta_a_i, with zero endpoint C",
        "original_difference": [str(v) for v in diff],
        "potential_prefixes": [str(v) for v in prefix],
        "reconstructed_difference": [str(v) for v in reconstructed],
    })

symmetric = all(
    a.get((i, j), Q(0)) == a.get((8 - j, 8 - i), Q(0))
    for i in range(9) for j in range(i + 1, 9)
)
assert symmetric
moment = sum(i * coef for (i, j), coef in a.items())
symmetry_moment = sum(Q(8 - s, 2) * Q(masses[str(s)]) for s in range(1, 9))
assert range_bound == moment == symmetry_moment == Q(2799999999999997, 10**14)

c0 = Q(893029029923108825, 10**20)
kappa = Q(3337881639516708570682858853672166187793,
          4955348548503844558750000000000000000000)
targets = []
with localcontext() as ctx:
    ctx.prec = 45
    for dk in [Q(1, 10**8), Q(1, 10**6), Q(1, 10**5), Q(1, 10**4)]:
        dc = (1 - c0) * dk / (kappa + dk)
        assert kappa * dc / (1 - c0 - dc) == dk
        targets.append({
            "delta_kappa_absolute": str(dk),
            "delta_percentage_points": str(100 * dk),
            "required_delta_c": str(dc),
            "required_delta_c_decimal": str(Decimal(dc.numerator) / Decimal(dc.denominator)),
        })

line_of = lambda needle: text[:text.index(needle)].count("\n") + 1
result = {
    "status": "PASS_exact_rational_coefficients_only",
    "scope": "No kernel evaluation, optimizer, scan, Lean or new zero proportion",
    "source_path": SOURCE.relative_to(ROOT).as_posix(),
    "source_sha256": sha,
    "source_lines": {
        "w_definition": line_of("def wfun (x : ℝ) : ℝ := kfun x ^ 2"),
        "w_nonnegative": line_of("lemma wfun_nonneg (x : ℝ)"),
        "k_abs_le_one": line_of("lemma abs_kfun_le_one (x : ℝ)"),
        "Fw_definition": line_of("def Fw (W : WCert n)"),
        "TS": text[:start].count("\n") + 1 + part[:re.search(r"^def TS :", part, re.M).start()].count("\n"),
        "current_certificate": line_of("theorem cert_AM : ∀ g : Fin 8"),
        "remainder_bound": line_of("theorem remainder_bound_n"),
        "actual_defect_estimate": line_of("theorem actual_defect_estimate"),
    },
    "nonzero_a_terms": len(a),
    "span_masses": masses,
    "reflection_symmetric": symmetric,
    "canonical_potential_range": {"lower": str(-range_bound), "upper": "0"},
    "coefficient_checks": coefficient_checks,
    "targets": targets,
    "paper_theorems_status": "Derived on paper in ANALYSIS.zh.md; not Lean formalized",
}
out = HERE / "exact-ledger-audit.json"
out.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"status": result["status"], "source_sha256": sha,
                  "span_masses": masses, "C": str(range_bound),
                  "receipt_sha256": hashlib.sha256(out.read_bytes()).hexdigest()}, ensure_ascii=False))
