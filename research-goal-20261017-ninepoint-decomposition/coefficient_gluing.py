"""One fixed coefficient LP: ten deletion embeddings of the proved W9 floor.

The LP discovers coefficients only. Fraction checks of primal and dual data
are authoritative for this finite family. No actual kernel, tree or Lean.
"""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR
import ast
import hashlib
import json
import re
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def pin(path):
    raw = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest()}


def main():
    output = HERE / "coefficient-gluing.json"
    assert not output.exists(), "One execution only; preserve existing receipt"
    oldpath = ROOT / "GramDefect20261015/Core.lean"
    wrap = ROOT / "StructuralW10Cert20261016/FinalConditional.lean"
    text = oldpath.read_text(encoding="utf-8")
    section = text.split("namespace AMW.Cert.PC9QB6M\n", 1)[1]
    terms = ast.literal_eval(re.search(r"^def TS : List Term := (\[[^\n]*\])$", section, re.M)[1])
    bs = ast.literal_eval(re.search(r"^def BS : List ℕ := (\[[^\n]*\])$", section, re.M)[1])
    sa = int(re.search(r"^def SA : ℕ := (\d+)$", section, re.M)[1])
    cn = int(re.search(r"^def cN : ℕ := (\d+)$", section, re.M)[1])
    c9 = F(cn, sa)
    total_pair_mass = sum((F(w, sa) for _, _, w, _ in terms), F(0))
    old_span_masses = [sum((F(w, sa) for i, j, w, _ in terms if j-i == d), F(0)) for d in range(1, 9)]
    assert all(0 < mass <= 2 for mass in old_span_masses)
    wrapper = wrap.read_text(encoding="utf-8")
    hw = F(int(re.search(r"def windowFloor : ℝ := (\d+) / 10 \^ 40", wrapper)[1]), 10**40)
    record = re.search(r"def currentSiteRatio : ℝ :=\s*(\d+) / (\d+)", wrapper)
    record = F(int(record[1]), int(record[2]))
    goal = record + F(1, 100000)
    columns = []
    matrices = []
    pressures = []
    for omitted in range(10):
        image = [i for i in range(10) if i != omitted]
        a = {(image[i], image[j]): F(w, sa) for i, j, w, _ in terms}
        b = [F(0) for _ in range(9)]
        for i, weight in enumerate(bs):
            for r in range(image[i], image[i+1]):
                b[r] += F(weight, sa)
        mass = [sum((w for (i, j), w in a.items() if j-i == d), F(0)) for d in range(1, 10)]
        assert sum(mass, F(0)) == total_pair_mass
        expected_B = F(sum(bs), sa) + (F(bs[omitted-1], sa) if 0 < omitted < 9 else 0)
        assert sum(b, F(0)) == expected_B
        columns.append({"omitted": omitted, "image": image,
                        "span_masses": list(map(str, mass)),
                        "pulled_pressure_by_gap": list(map(str, b)),
                        "total_pressure": str(expected_B)})
        matrices.append(mass)
        pressures.append(expected_B)
    A = [[matrices[k][d] for k in range(10)] for d in range(9)]
    gains = [goal*c9 - b for b in pressures]
    threshold = goal - hw
    total_weight_upper = F(18)/total_pair_mass
    assert c9*total_weight_upper < F(1, 64)
    # Only this call is an optimizer invocation. Everything after it is
    # deterministic rational reconstruction/checking of that fixed output.
    import numpy as np
    import scipy
    from scipy.optimize import linprog
    started = time.monotonic()
    result = linprog(-np.array(list(map(float, gains))),
                     A_ub=np.array([[float(v) for v in row] for row in A]),
                     b_ub=np.full(9, 2.0), bounds=(0, None), method="highs")
    elapsed = time.monotonic() - started
    assert result.success, result.message
    DL = 10**18
    def rounded(x, mode):
        return F(int((Decimal(str(max(0.0, float(x))))*DL).to_integral_value(rounding=mode)), DL)
    lam = [rounded(x, ROUND_FLOOR) for x in result.x]
    row_load = [sum((a*x for a, x in zip(row, lam)), F(0)) for row in A]
    scale = min([F(1)] + [F(2)/x for x in row_load if x > 0])
    lam = [x*scale for x in lam]
    row_load = [sum((a*x for a, x in zip(row, lam)), F(0)) for row in A]
    assert all(0 <= x <= 2 for x in row_load) and all(x >= 0 for x in lam)
    floor = c9*sum(lam, F(0))
    pressure = sum((x*b for x, b in zip(lam, pressures)), F(0))
    assert 0 < floor < F(1, 64)
    ratio = (hw-pressure)/(1-floor)
    dual = [rounded(-x, ROUND_CEILING) for x in result.ineqlin.marginals]
    before = [sum((A[d][k]*dual[d] for d in range(9)), F(0)) for k in range(10)]
    repair = max([F(0)] + [(gains[k]-before[k])/sum(matrices[k], F(0)) for k in range(10)])
    dual = [y+repair for y in dual]
    covered = [sum((A[d][k]*dual[d] for d in range(9)), F(0)) for k in range(10)]
    assert all(y >= 0 for y in dual) and all(x >= g for x, g in zip(covered, gains))
    dual_upper = 2*sum(dual, F(0))
    impossible_at_goal = dual_upper <= threshold
    passes = ratio > goal
    assert not (passes and impossible_at_goal)
    data = {
        "schema": "one-fixed-ten-embedding-global-coefficient-LP-v1",
        "source_files": [pin(oldpath), pin(wrap), pin(Path(__file__))],
        "scipy_version": scipy.__version__, "numpy_version": np.__version__,
        "points": 10, "ordered_deletion_embeddings": columns,
        "old_proved_floor": str(c9), "window_floor": str(hw),
        "record": str(record), "required_strict_target": str(goal),
        "LP_variables": 10, "LP_capacity_rows": 9, "optimizer_calls": 1,
        "solver_success": bool(result.success), "solver_message": result.message,
        "solver_seconds": elapsed, "raw_primal": result.x.tolist(),
        "raw_dual_minimize_marginals": result.ineqlin.marginals.tolist(),
        "raw_minimize_objective": float(result.fun),
        "quantization_denominator": DL, "primal_scale": str(scale),
        "exact_primal_weights": list(map(str, lam)),
        "exact_primal_capacity_loads": list(map(str, row_load)),
        "exact_primal_floor": str(floor), "exact_primal_pressure": str(pressure),
        "exact_primal_ratio": str(ratio), "primal_percent_hint": float(100*ratio),
        "exact_primal_exceeds_strict_goal": passes,
        "exact_linearized_column_gains": list(map(str, gains)),
        "exact_dual_nonnegative_weights": list(map(str, dual)),
        "exact_dual_uniform_repair": str(repair),
        "exact_dual_covered_column_gains": list(map(str, covered)),
        "exact_dual_upper": str(dual_upper), "exact_required_threshold": str(threshold),
        "exact_strict_gap_threshold_minus_upper": str(threshold-dual_upper),
        "family_cannot_reach_record_plus_one_over_100000": impossible_at_goal,
        "old_exact_span_masses": list(map(str, old_span_masses)),
        "old_exact_total_pair_mass": str(total_pair_mass),
        "all_capacity_rows_sum_implies_total_weight_at_most": str(total_weight_upper),
        "pre_solver_failed_executions": 1,
        "pre_solver_failure_receipt": "research-goal-20261017-ninepoint-decomposition/presolver-failure.json",
        "all_admissible_family_floors_below_one_over_64": True,
        "actual_kernel_evaluations": 0, "tree_records_read": 0, "Lean_invocations": 0,
        "new_global_floor_Lean_proven": False,
        "new_unconditional_zero_proportion_proven": False,
        "website_submission_ready": False,
        "no_automatic_point_count_target_kernel_or_embedding_family_rerun": True,
    }
    output.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"one_solver_call": True, "seconds": elapsed,
                      "candidate_percent_hint": data["primal_percent_hint"],
                      "candidate_passes_goal_exactly": passes,
                      "exact_dual_rules_out_goal_for_family": impossible_at_goal,
                      "exact_gap_hint": float(threshold-dual_upper)}))


if __name__ == "__main__":
    main()
