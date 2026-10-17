"""Exact integer-index budget; no kernel, optimizer, tree, witness or Lean."""
from pathlib import Path
from fractions import Fraction as F
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def pin(path):
    raw = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest()}


def main():
    path = ROOT / "research-20261016-followup/window_reweight_rational.json"
    data = json.loads(path.read_bytes())
    scale = data["denominator"]
    bs = [F(b, scale) for b in data["b_numerators"]]
    assert len(bs) == 9 and min(bs) > 0
    B = sum(bs, F())
    sep = F(123, 128)
    assert B == F(11055671, 2500000000)
    assert (1-sep)*B == F(11055671, 64000000000)
    cases = []
    for c in [F(11, 1250), F(221, 25000)]:
        budget = c-sep*B
        assert budget > 0
        rows = []
        for i, j, weight in data["a_upper"]:
            if not weight:
                continue
            distance = j-i
            bound = distance+budget/min(bs[i:j])
            upper = -((-bound.numerator)//bound.denominator)
            rows.append({"pair": [i, j], "positive_weight": str(F(weight, scale)),
                         "strict_interpolation_argument_upper": str(bound),
                         "smallest_integer_argument": distance,
                         "largest_integer_argument_upper": upper})
        assert len(rows) == 41 and max(r["largest_integer_argument_upper"] for r in rows) == 32
        cases.append({"floor": str(c), "excess_pressure_budget": str(budget),
                      "positive_pairs": rows, "max_integer_argument": 32})
    result = {"schema": "common-shift-rounding-exact-integer-index-budget-v1",
              "dependency_files": [pin(path)], "source": pin(Path(__file__)),
              "separation": str(sep), "pressure_sum": str(B),
              "fixed_rounding_pressure_cost": str((1-sep)*B),
              "minimum_pressure_coefficient": str(min(bs)), "cases": cases,
              "actual_integer_values_checked_here": False,
              "claim": "Only integer arguments1..32 are required under either sublevel budget; actual values and formal consumers remain separate obligations.",
              "optimizer_calls": 0, "actual_kernel_evaluations": 0, "tree_records_read": 0,
              "new_partition_or_witness_generated": False, "Lean_invocations": 0,
              "global_rounding_inequality_Lean_proven": False,
              "new_global_floor_proven": False,
              "new_unconditional_zero_proportion_proven": False, "website_submission_ready": False}
    raw = (json.dumps(result, indent=2) + "\n").encode()
    output = HERE / "geometry-budget.json"
    assert not output.exists(), "Preserve frozen budget"
    output.write_bytes(raw)
    print(json.dumps({"max_integer_arguments": [32, 32],
                      "pressure_cost": str((1-sep)*B),
                      "receipt_sha256": hashlib.sha256(raw).hexdigest()}))


if __name__ == "__main__":
    main()
