"""Static record-source overlap arithmetic; no walk/literal payload decoding.

Reads only coefficient declarations and theorem signatures.  No numerical
kernel evaluation, optimization, leaf enumeration, Lean, or network access.
"""
import ast
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SOURCE = "research-goal-20261018-record-source-audit/snapshot/Solution.lean"
EXPECTED_SHA = "f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf"


def pin(relative):
    raw = (ROOT / relative).read_bytes()
    return {"path": relative, "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest()}


def main():
    output = HERE / "static-receipt.json"
    assert not output.exists(), "Preserve frozen receipts"
    raw = (ROOT / SOURCE).read_bytes()
    assert len(raw) == 1818411 and hashlib.sha256(raw).hexdigest() == EXPECTED_SHA
    src = raw.decode("utf-8")
    section = src.split("namespace AMW.Cert.PC9QB6M\n", 1)[1]
    cn = int(re.search(r"^noncomputable def cN : ℕ := (\d+)$", section, re.M)[1])
    sa = int(re.search(r"^noncomputable def SA : ℕ := (\d+)$", section, re.M)[1])
    bN = ast.literal_eval(re.search(r"^noncomputable def BS : List ℕ := (\[[^\n]*\])$", section, re.M)[1])
    terms = ast.literal_eval(re.search(r"^noncomputable def TS : List Term := (\[[^\n]*\])$", section, re.M)[1])
    smax = ast.literal_eval(re.search(r"^noncomputable def SMAX .*?: ℕ := (\[[^\n]*\])", section, re.M)[1])
    c9 = F(cn, sa)
    b = [F(x, sa) for x in bN]
    B9 = sum(b, F(0))
    H = F(6721290091768038344368273523390880473594, 10**40)
    R = F(3337839448633819172184136761695440236797,
          4955319193847235264050000000000000000000)
    assert (H - B9) / (1 - c9) == R
    target = R + F(1, 10**6)
    need = (target - H + B9) / target
    need_increment = need - c9
    assert need_increment == (1 - c9) * F(1, 10**6) / target
    # A single fixed rational opportunity target, not an optimization or scan.
    delta = F(3, 2 * 10**6)
    c = c9 + delta
    t = 2 * c - c9
    assert c > need and (H - B9) / (1 - c) > target
    sep = F(17, 20)
    assert c < F(1, 64)
    spans = [sum((F(w, sa) for i, j, w, _ in terms if j - i == d), F(0))
             for d in range(1, 10)]
    assert len(b) == 8 and len(terms) == 34
    assert all(0 <= x <= 2 for x in spans)
    # Fixed prefix/suffix endpoint embeddings do not change rank spans.
    for omit in [0, 9]:
        image = [j for j in range(10) if j != omit]
        mapped = [sum((F(w, sa) for i, j, w, _ in terms
                       if image[j] - image[i] == d), F(0))
                  for d in range(1, 10)]
        assert mapped == spans
    unary = c9 + sep * B9
    tails = [br * F(M, 32768) + sep * (B9 - br) for br, M in zip(b, smax)]
    assert unary > t and len(tails) == 8 and min(tails) > t and sep > F(1, 2)
    cert_signature = re.search(r"theorem cert_AM :.*? := by", src, re.S)[0]
    assert "∀ g : Fin 8 → ℝ" in cert_signature and "(∀ i, 0 ≤ g i)" in cert_signature
    assert "theorem PC9QB6M_G_rev" in src
    assert "theorem kernel_square_ge {t : ℝ} (ht : |t| ≤ 17 / 20)" in src
    assert "(1 / 64 : ℝ) ≤ AMW.kfunAM t ^ 2" in src
    assert "(TS : List Term) (cN : ℕ)" in src
    assert "walkCutR TOP BK TOPD BKD PT REG" in src
    # Existing local files are cost/reference bodies only, not same-kernel imports.
    bridge_paths = ["GramDefect20261015/RefinedCounting.lean",
        "StructuralResearch20261016/Coboundary.lean",
        "StructuralResearch20261016/CoboundaryCounting.lean"]
    bridges = [pin(x) for x in bridge_paths]
    bridge_sum = sum(x["bytes"] for x in bridges)
    assert bridge_sum == 38361
    lines = src.splitlines()
    names = ["noncomputable def cAMn", "noncomputable def vAM", "noncomputable def cN :",
        "noncomputable def BS :", "noncomputable def TS :", "noncomputable def mcheckGX",
        "noncomputable def mleafP", "noncomputable def leafStep", "noncomputable def walkCutR",
        "noncomputable def COV :", "noncomputable def SMAX", "theorem cert_AM :",
        "theorem PC9QB6M_G_rev", "theorem kernel_square_ge", "theorem actual_dyadic {n : ℕ}"]
    anchors = {name: [i for i, line in enumerate(lines, 1) if name in line] for name in names}
    result = {
        "schema": "new-record-fixed-overlap-static-review-v1",
        "source": pin(SOURCE),
        "fixed_upstream_commit": "cfc7ce6113199b7d5f262812d81089778e84335c",
        "source_identity_and_signatures_only_not_kernel_acceptance": True,
        "profile_terms": 13, "old_profile_terms_not_reused": True,
        "new_c9": str(c9), "new_total_pressure_B9": str(B9), "new_window_floor_H": str(H),
        "record_ratio_recovered_from_source_parameters": str(R),
        "target_absolute_increment": "1/1000000", "target_strict_ratio": str(target),
        "necessary_joint_floor_strict_gt": str(need),
        "necessary_increment_over_new_c9_strict_gt": str(need_increment),
        "necessary_increment_hint": float(need_increment),
        "fixed_opportunity_increment": str(delta), "fixed_candidate_c": str(c),
        "fixed_two_sublevel_threshold_t": str(t),
        "fixed_t_scaled_integer": str(t * sa),
        "ratio_if_joint_floor_proven": str((H - B9) / (1 - c)),
        "ratio_if_joint_floor_proven_percent_hint": float(100 * (H - B9) / (1 - c)),
        "fixed_separation": str(sep),
        "new_source_original_short_pair_floor": "1/64",
        "existing_new_source_pair_payment_suffices_at_original_separation": True,
        "new_kernel_short_pair_payment_at_123_over_128_proven_by_this_review": False,
        "prefix_suffix_weights": {"delete0": "1/2", "delete9": "1/2"},
        "prefix_suffix_span_masses": list(map(str, spans)),
        "prefix_suffix_pressure": str(B9),
        "new_root_unary_guard_with_separated_pressure": str(unary),
        "new_root_tail_guards_with_separated_pressure": list(map(str, tails)),
        "new_root_pre_guard_margin_checks_pass": True,
        "expected_original_terminal_leaf_count_from_task": 13046,
        "terminal_leaf_count_independently_replayed": False,
        "nested_cut_states_require_original_full_identity_replay": True,
        "source_anchors": anchors,
        "website_source_cap_bytes": 2000000,
        "new_source_bytes": len(raw), "new_source_raw_remaining_bytes": 2000000 - len(raw),
        "existing_bridge_body_cost_references_only": bridges,
        "existing_bridge_bodies_raw_bytes": bridge_sum,
        "new_source_plus_reference_bodies_raw_bytes": len(raw) + bridge_sum,
        "raw_remaining_before_all_new_classification_and_joint_proof": 2000000 - len(raw) - bridge_sum,
        "actual_migrated_single_source_built": False,
        "new_global_sublevel_cover_proven": False,
        "new_global_joint_floor_proven": False,
        "new_optimizer_calls": 0, "new_actual_kernel_evaluations": 0,
        "leaf_or_literal_payloads_decoded": 0, "new_overlap_checks": 0,
        "Lean_invocations": 0, "website_submission_ready": False,
    }
    output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"path": output.relative_to(ROOT).as_posix(),
        "source_sha256": EXPECTED_SHA, "original_sep_pairpayment": "available",
        "fixed_c": str(c), "fixed_t": str(t), "new_leaf_decodes": 0}))


if __name__ == "__main__":
    main()
