"""Analyze fixed certificate ceilings; this proves no stronger zero proportion.

Thresholds and scores use Fraction/integer arithmetic. Decimal strings are
display only. The two input receipts and this script are SHA256-bound.
"""
from pathlib import Path
from fractions import Fraction as Q
from decimal import Decimal, localcontext
from math import factorial
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
INPUTS = ["verification/gram-defect-20261015/finite-margin.json",
          "verification/gram-defect-20261015/exact-score.json"]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dec(value):
    with localcontext() as context:
        context.prec = 70
        return str(Decimal(value.numerator) / Decimal(value.denominator))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default=str(ROOT / "output/fixed-certificate-potential-20261015.json"))
    args = parser.parse_args()
    assert __debug__, "Run with assertions enabled"
    hashes = {name: sha(ROOT / name) for name in INPUTS}
    finite, exact = [json.loads((ROOT / name).read_text(encoding="utf8")) for name in INPUTS]
    h, pressure, current_c = map(Q, [exact["window_floor"], exact["pressure"], exact["local_floor"]])
    denominator = finite["objective_denominator"]
    old, current, slope = (finite[key] for key in
                          ["source_original_cN", "candidate_cN", "threshold_slope"])
    assert current_c == Q(current, denominator) and len(finite["per_root"]) == 48
    assert len(finite["all_root_conditions"]) == 108 and slope > 0 and h > pressure

    def score(numerator):
        assert 0 <= numerator < denominator
        return (h-pressure) / (1-Q(numerator, denominator))

    current_score = score(current)
    assert current_score == Q(int(exact["numerator"]), int(exact["denominator"]))
    limits = [(row, old+row["min_margin"]//slope) for row in finite["per_root"]]
    assert min(limit for _, limit in limits) == current

    def impact(limit):
        value = score(limit)
        return {"max_cN": str(limit), "headroom_cN_over_current": str(limit-current),
                "conditional_kappa_exact": str(value), "conditional_kappa_decimal": dec(value),
                "conditional_percentage": dec(100*value),
                "conditional_gain_pp_exact": str(100*(value-current_score)),
                "conditional_gain_percentage_points_over_current": dec(100*(value-current_score))}

    tightest = [{"root": row["root"], "bottleneck_position": row["minimum_margin_position"],
                 "minimum_original_margin": str(row["min_margin"]), **impact(limit)}
                for row, limit in sorted(limits, key=lambda pair: pair[1])[:5]]
    condition_limit = min(row[-1] for row in finite["all_root_conditions"])
    assert condition_limit == finite["root_condition_minimum"][-1]
    condition_records = [row for row in finite["all_root_conditions"] if row[-1] == condition_limit]

    # With PAMhi and pi-upper fixed, alternating next terms enclose the exact
    # cosine/sinc values at theta^2=1/2. This is a research arithmetic analysis,
    # not an additional Lean theorem or an improvement added to the record.
    cosine = sum(Q((-1)**j, 2**j*factorial(2*j)) for j in range(17))
    sinc = sum(Q((-1)**j, 2**j*factorial(2*j+1)) for j in range(18))
    pi_upper = Q(314159265358979323847, 10**20)
    coefficients = [12310798, -15041681, 3867664, 6489926, -992327, 5580097,
                    -6846472, 3781297, -5670353, 3355089, -450523, -218483]
    pam_upper = sum(Q(a, 10**9)**2 * (Q(1, 2)-1/(4*pi_upper**2*j*j))
                    for j, a in enumerate(coefficients, 1))
    enclosure = lambda c, s: Q(3, 2)-c/s-pam_upper/s**2
    cosine_lower = cosine-Q(1, 2**17*factorial(34))
    sinc_upper = sinc+Q(1, 2**18*factorial(37))
    window_lower = enclosure(cosine, sinc)
    window_cap = enclosure(cosine_lower, sinc_upper)
    assert 0 < cosine_lower <= cosine and 0 < sinc <= sinc_upper and pam_upper >= 0
    assert h <= window_lower <= window_cap < h+Q(1, 10**40)
    assert hashes == {name: sha(ROOT / name) for name in INPUTS}
    result = {
        "analysis_kind": "conditional_fixed_certificate_analysis_not_a_new_lower_bound",
        "input_sha256": hashes, "script_sha256": sha(Path(__file__)),
        "arithmetic": "Integer thresholds and Fraction scores; Decimal display only",
        "fixed_window_floor": str(h), "fixed_pressure": str(pressure),
        "objective_denominator": str(denominator), "source_original_cN": str(old),
        "current_cN": str(current), "current_certified_kappa": str(current_score),
        "threshold_slope": str(slope), "formula": "kappa=(h-B)/(1-cN/objective_denominator)",
        "five_tightest_roots": tightest,
        "fixed_root_condition_cap": {"condition_records": condition_records, **impact(condition_limit)},
        "local_sensitivity_dkappa_dc_exact": str((h-pressure)/(1-current_c)**2),
        "local_sensitivity_dkappa_dc_decimal": dec((h-pressure)/(1-current_c)**2),
        "further_trigonometric_refinement_with_fixed_pam_upper": {
            "pi_upper": str(pi_upper), "pam_upper": str(pam_upper),
            "cosine_next_term": str(cosine-cosine_lower), "sinc_next_term": str(sinc_upper-sinc),
            "window_cap_exact": str(window_cap),
            "max_window_gain_over_current_floor_exact": str(window_cap-h),
            "max_window_gain_over_current_floor_decimal": dec(window_cap-h),
            "max_gain_percentage_points_over_current": dec(100*(window_cap-h)/(1-current_c)),
            "can_raise_current_window_numerator_at_denominator_10_pow_40": False},
        "interpretation": [
            "Each root ceiling concerns its unchanged finite witnesses at the fixed denominator.",
            "A larger row value is infeasible jointly with the currently unchanged tighter roots.",
            "Changing one limiting leaf need not reach the next root ceiling; other leaves may intervene.",
            "The cover cap assumes all conflicting root witnesses have been strengthened while the present cover, weights, pressure and window remain fixed.",
            "These are research bottlenecks and conditional caps, not achieved lower bounds or global mathematical upper bounds."],
        "new_stronger_lower_bound_proved": False, "included_in_current_certified_gain": False,
        "inputs_unchanged": True}
    encoded = json.dumps(result, indent=2)+"\n"
    if args.output == "-":
        print(encoded, end="")
    else:
        target = Path(args.output)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(encoded, encoding="utf8", newline="\n")
        print(json.dumps({"output": str(target), "exact_arithmetic_checks_passed": True,
                          "new_stronger_lower_bound_proved": False}))


if __name__ == "__main__":
    main()
