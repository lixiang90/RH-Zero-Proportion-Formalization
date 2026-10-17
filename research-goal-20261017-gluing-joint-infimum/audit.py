"""Static exact audit of the already frozen support {0,1}; no numerical oracle.

This verifies pullback/lifting matrices and exact target arithmetic.  The
functional identity is proved in NOTE.zh.md, not claimed as a Lean theorem.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def pin(relative):
    raw = (ROOT / relative).read_bytes()
    return {"path": relative, "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest()}


def main():
    output = HERE / "exact-replay.json"
    assert not output.exists(), "Do not replace a frozen replay"
    upstream = "research-goal-20261017-ninepoint-decomposition/coefficient-gluing.json"
    core = "GramDefect20261015/Core.lean"
    data = json.loads((ROOT / upstream).read_text(encoding="utf-8"))
    source = (ROOT / core).read_text(encoding="utf-8")
    cert = re.search(r"theorem cert_AM :.*? := by", source, re.S)[0]
    assert "∀ g : Fin 8 → ℝ" in cert
    assert "(∀ i, 0 ≤ g i)" in cert
    assert "859538525913875481" in cert
    weights = list(map(F, data["exact_primal_weights"]))
    assert len(weights) == 10 and all(x >= 0 for x in weights)
    assert [i for i, x in enumerate(weights) if x] == [0, 1]
    S = sum(weights, F(0))
    assert S > 0
    h0 = [[int(j == i + 1) for j in range(9)] for i in range(8)]
    h1 = [row[:] for row in h0]
    h1[0][0] = 1
    lifting = [[0] * 8] + [[int(j == i) for j in range(8)] for i in range(8)]

    def matmul(a, b):
        return [[sum(x * y for x, y in zip(row, col))
                 for col in zip(*b)] for row in a]

    identity = [[int(i == j) for j in range(8)] for i in range(8)]
    assert matmul(h0, lifting) == identity
    assert matmul(h1, lifting) == identity
    assert all(x >= 0 for row in h0 + h1 + lifting for x in row)
    c9 = F(data["old_proved_floor"])
    H = F(data["window_floor"])
    K = F(data["required_strict_target"])
    B = F(data["exact_primal_pressure"])
    existing_floor = F(data["exact_primal_floor"])
    assert existing_floor == c9 * S
    needed_floor = (K - H + B) / K
    needed_old_floor = needed_floor / S
    dual_gap = F(data["exact_strict_gap_threshold_minus_upper"]) / K
    assert needed_old_floor > c9
    assert needed_floor - existing_floor >= dual_gap > 0
    result = {
        "schema": "fixed-saved-gluing-support-joint-infimum-static-v1",
        "scope": "Saved exact primal weights only: ordered deletions 0 and 1",
        "source_files": [pin(upstream), pin(core), pin(
            "research-goal-20261017-ninepoint-decomposition/NOTE.zh.md")],
        "cert_AM_domain": "all eight gaps nonnegative; no positive-separation hypothesis",
        "positive_weight_indices": [0, 1],
        "exact_positive_weights": [str(weights[0]), str(weights[1])],
        "total_weight": str(S),
        "deletion0_pullback": h0,
        "deletion1_pullback": h1,
        "canonical_lifting": lifting,
        "both_pullbacks_composed_with_lifting_are_identity": True,
        "all_maps_preserve_nonnegative_orthants": True,
        "global_lower_bound_equivalence":
            "forall g>=0, F_lambda(g)>=L iff forall h>=0, F9(h)>=L/S",
        "infimum_identity": "inf_{g>=0} F_lambda = S * inf_{h>=0} F9",
        "no_joint_frustration_gain_for_saved_support": True,
        "old_certified_c9": str(c9),
        "old_actual_infimum_known_equal_to_c9": False,
        "window_floor_H": str(H),
        "required_strict_ratio_K": str(K),
        "saved_total_pressure_B": str(B),
        "existing_reused_floor": str(existing_floor),
        "needed_total_floor_strictly_greater_than": str(needed_floor),
        "needed_total_floor_hint": float(needed_floor),
        "needed_extra_total_floor_strictly_greater_than": str(needed_floor - existing_floor),
        "needed_extra_total_floor_hint": float(needed_floor - existing_floor),
        "needed_old_global_floor_strictly_greater_than": str(needed_old_floor),
        "needed_old_global_floor_hint": float(needed_old_floor),
        "needed_old_floor_increment_strictly_greater_than": str(needed_old_floor - c9),
        "needed_old_floor_increment_hint": float(needed_old_floor - c9),
        "strictly_positive_gaps_scope":
            "Same infimum by continuity of the old finite energy; proof in note, not Lean",
        "other_supports_excluded": False,
        "new_optimizer_calls": 0,
        "new_actual_kernel_evaluations": 0,
        "new_tree_or_cover_records_read": 0,
        "Lean_invocations": 0,
        "new_global_floor_Lean_proven": False,
        "new_unconditional_zero_proportion_proven": False,
        "website_submission_ready": False,
    }
    output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"path": output.relative_to(ROOT).as_posix(),
                      "support": [0, 1], "lifting_checked": True,
                      "needed_old_floor": str(needed_old_floor),
                      "new_optimizer_calls": 0}, ensure_ascii=False))


if __name__ == "__main__":
    main()
