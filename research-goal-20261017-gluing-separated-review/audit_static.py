"""Fixed-coefficient separated-domain arithmetic and source API inventory.

No compressed walk decoding, new kernel value, optimizer, enumeration or Lean.
"""
import ast
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
    output = HERE / "exact-static.json"
    assert not output.exists(), "Preserve frozen receipts"
    core_path = "GramDefect20261015/Core.lean"
    primal_path = "research-goal-20261017-ninepoint-decomposition/coefficient-gluing.json"
    core = (ROOT / core_path).read_text(encoding="utf-8")
    section = core.split("namespace AMW.Cert.PC9QB6M\n", 1)[1]
    bsN = ast.literal_eval(re.search(r"^def BS : List ℕ := (\[[^\n]*\])$", section, re.M)[1])
    ts = ast.literal_eval(re.search(r"^def TS : List Term := (\[[^\n]*\])$", section, re.M)[1])
    sa = int(re.search(r"^def SA : ℕ := (\d+)$", section, re.M)[1])
    smax = ast.literal_eval(re.search(r"^def SMAX .*?: ℕ := (\[[^\n]*\])", core, re.M)[1])
    old = json.loads((ROOT / primal_path).read_text(encoding="utf-8"))
    lam = list(map(F, old["exact_primal_weights"]))
    assert [i for i, x in enumerate(lam) if x] == [0, 1]
    S = sum(lam, F(0))
    b = [F(x, sa) for x in bsN]
    B9 = sum(b, F(0))
    s = F(123, 128)
    A0 = sum((F(w, sa) for i, j, w, _ in ts if i == 0), F(0))
    shift_cost = b[0] * s + A0
    small_joint_upper = lam[1] * shift_cost
    c9 = F(old["old_proved_floor"])
    H = F(old["window_floor"])
    K = F(old["required_strict_target"])
    savedB = F(old["exact_primal_pressure"])
    saved_need = (K - H + savedB) / K
    separated_m9_necessary = (saved_need - small_joint_upper) / S
    # A fixed proposed opportunity gate, not an optimized or scanned target.
    c = F(8611, 10**6)
    t = 2 * c - c9
    pair_need = (K - H + B9) / K
    pair_ratio = (H - B9) / (1 - c)
    pairpay = F(433, 50000)
    assert c > pair_need and pair_ratio > K and c <= pairpay
    assert (t * sa).denominator == 1
    span_mass = [sum((F(w, sa) for i, j, w, _ in ts if j - i == d), F(0))
                 for d in range(1, 10)]
    assert all(0 <= x <= 2 for x in span_mass)
    # Endpoint embeddings have the same rank-span mass and total pressure.
    for k in [0, 9]:
        col = old["ordered_deletion_embeddings"][k]
        assert list(map(F, col["span_masses"])) == span_mass
        assert F(col["total_pressure"]) == B9
    tail_guards = [br * F(M, 32768) + s * (B9 - br)
                   for br, M in zip(b, smax)]
    unary_true_guard = c9 + s * B9
    assert len(tail_guards) == 8 and min(tail_guards) > t
    assert unary_true_guard > t and s > F(1, 2)
    matching = (ROOT / "StructuralW10Followup20261016/MatchingThreshold.lean").read_text(encoding="utf-8")
    pair_src = (ROOT / "StructuralW10Followup20261016/KernelPair123128.lean").read_text(encoding="utf-8")
    assert "{c C B hw sep : ℝ}" in matching
    assert "(hCert : SeparatedSummedCertificate W c C sep)" in matching
    assert "(hpair : ∀ t : ℝ, |t| ≤ sep → c ≤ wfun t)" in matching
    assert "(433 / 50000 : ℝ) ≤ wfun t" in pair_src
    assert "def mcheckGX" in core and "(TS : List Term) (cN : ℕ)" in core
    assert "{TS : List Term} {cN : ℕ}" in core
    assert "abbrev Covered : Cl → Prop := CovBy 8 PR (Pg cN 8 BS TS)" in core
    bridge_paths = ["GramDefect20261015/RefinedCounting.lean",
        "StructuralResearch20261016/Coboundary.lean",
        "StructuralResearch20261016/CoboundaryCounting.lean",
        "StructuralW10Followup20261016/MatchingThreshold.lean",
        "StructuralW10Followup20261016/KernelPair123128.lean",
        "GramDefect20261015/SharpWindow.lean"]
    bridge_rows = [pin(x) for x in bridge_paths]
    core_bytes = len((ROOT / core_path).read_bytes())
    literal_existing_source_bytes = core_bytes + sum(x["bytes"] for x in bridge_rows)
    assert core_bytes == 1912350 and literal_existing_source_bytes == 1971160
    result = {
        "schema": "gluing-separated-static-opportunity-review-v1",
        "separation": str(s),
        "domain_correction": "Zero-gap lifting and merely strict positivity no-go do not apply to fixed g_r>=123/128",
        "saved_support": [0, 1], "saved_weight_sum": str(S),
        "old_endpoint_pressure": str(b[0]),
        "old_endpoint_pair_mass_A0": str(A0),
        "endpoint_shift_cost_upper": str(shift_cost),
        "saved_separated_infimum_bracket": "S*m9(s) <= inf_{g>=s} F_lambda <= S*m9(s)+lambda1*(b0*s+A0)",
        "saved_pure_frustration_upper": str(small_joint_upper),
        "saved_pure_frustration_upper_hint": float(small_joint_upper),
        "necessary_old_separated_infimum_for_saved_target_strict_gt": str(separated_m9_necessary),
        "necessary_old_separated_infimum_hint": float(separated_m9_necessary),
        "necessary_increment_over_c9_hint": float(separated_m9_necessary - c9),
        "old_separated_infimum_known_equal_to_c9": False,
        "generic_old_kernel_separated_counting_API_present": True,
        "old_kernel_pair_payment": str(pairpay),
        "proposed_prefix_suffix_weights": {"delete0": "1/2", "delete9": "1/2"},
        "prefix_suffix_total_pressure": str(B9),
        "prefix_suffix_span_masses": list(map(str, span_mass)),
        "prefix_suffix_capacity_checked_from_existing_columns": True,
        "proposed_fixed_floor_c": str(c),
        "required_prefix_suffix_floor_strict_gt": str(pair_need),
        "proposed_ratio_if_floor_proven": str(pair_ratio),
        "proposed_ratio_percent_hint": float(100 * pair_ratio),
        "proposed_ratio_exceeds_task_target": pair_ratio > K,
        "proposed_floor_below_existing_pair_payment": c <= pairpay,
        "necessary_each_window_sublevel_t": str(t),
        "t_scaled_integer": str(t * sa),
        "old_root_unary_true_guard_with_separated_pressure": str(unary_true_guard),
        "old_root_tail_guards_with_separated_pressure": list(map(str, tail_guards)),
        "all_old_root_guard_margins_positive_at_t": True,
        "low_level_leaf_checker_parameterizes_floor": True,
        "specialized_old_walk_parameterizes_floor": False,
        "exception_cells_extracted": False,
        "overlap_exclusion_proven": False,
        "single_source_cap_bytes": 2000000,
        "full_Core_bytes": core_bytes,
        "full_Core_alone_remaining_bytes": 2000000 - core_bytes,
        "existing_counting_bridge_modules": bridge_rows,
        "literal_existing_Core_plus_all_bridge_bytes": literal_existing_source_bytes,
        "literal_existing_source_remaining_for_new_proof_bytes": 2000000 - literal_existing_source_bytes,
        "size_scope": "Raw existing source sums only; no final flattened artifact, new partial-cover interpreter, exception data, overlap proof or top theorem counted",
        "new_actual_floor_full_root_export_size_known": False,
        "new_Lean_nanoda_Comparator_runtime_known": False,
        "source_files": [pin(x) for x in [core_path, primal_path,
            "StructuralResearch20261016/Coboundary.lean",
            "StructuralW10Followup20261016/MatchingThreshold.lean",
            "StructuralW10Followup20261016/KernelPair123128.lean",
            "GramDefect20261015/SharpWindow.lean",
            "GramDefect20261015/RefinedCounting.lean",
            "StructuralResearch20261016/CoboundaryCounting.lean",
            "research-goal-20261017-gluing-joint-infimum/joint-infimum-files.json"]],
        "new_optimizer_calls": 0, "new_actual_kernel_evaluations": 0,
        "new_compressed_walk_or_leaf_records_decoded": 0,
        "new_overlap_pair_checks": 0, "Lean_invocations": 0,
        "new_global_floor_Lean_proven": False,
        "new_unconditional_zero_proportion_proven": False,
        "website_submission_ready": False,
    }
    output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"path": output.relative_to(ROOT).as_posix(),
        "domain_correction": True, "prefix_suffix_c": str(c), "t": str(t),
        "root_pre_guards": "PASS with separated pressure", "new_leaf_decodes": 0}))


if __name__ == "__main__":
    main()
