"""Reproduce the new AMW window floor using exact integer arithmetic only.

This script is an independent arithmetic audit, not a replacement for the
Lean proof in GramDefect20261015/SharpWindow.lean.  The analytic inequalities
come from the inherited Meshuggah alternating-polynomial theorems.
"""
from __future__ import annotations

import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
import json
from math import factorial
from pathlib import Path


F = Fraction
DIGITS = 40
SCALE = 10 ** DIGITS
PREVIOUS_HW_NUMERATOR = 6721684105641188747759454444013516755656
NEW_HW_NUMERATOR = 6721684105641188747759983512104999330646
COEFFICIENT_NUMERATORS = (
    12310798, -15041681, 3867664, 6489926, -992327, 5580097,
    -6846472, 3781297, -5670353, 3355089, -450523, -218483,
)


def ratio(x: Fraction) -> str:
    return f"{x.numerator}/{x.denominator}"


def decimal(x: Fraction) -> str:
    with localcontext() as context:
        context.prec = 80
        return str(Decimal(x.numerator) / Decimal(x.denominator))


def compute() -> dict:
    # theta = sqrt(2)/2, hence theta^2 = 1/2 exactly.  An odd
    # number of cosine terms is an upper bound, an even number of
    # sinc terms is a lower bound, by the inherited Taylor sign theorem.
    cosine_upper = sum(
        (F((-1) ** j, 2 ** j * factorial(2 * j)) for j in range(17)), F(0)
    )
    sinc_lower = sum(
        (F((-1) ** j, 2 ** j * factorial(2 * j + 1)) for j in range(18)), F(0)
    )
    assert cosine_upper == F(
        132424952393242556021461169421128332043,
        174187298275621608010492925706240000000,
    )
    assert sinc_lower == F(
        14302403666080084620954960913502913904936237,
        15567659428162813657715716369101619200000000,
    )
    assert cosine_upper > 0 and sinc_lower > 0

    # Preserve the accepted source's proved Real.pi_lt_d20 bound.
    pi_upper = F(314159265358979323847, 10 ** 20)
    pam_upper = sum(
        (
            F(c, 10 ** 9) ** 2 * (F(1, 2) - 1 / (4 * pi_upper ** 2 * j ** 2))
            for j, c in enumerate(COEFFICIENT_NUMERATORS, 1)
        ),
        F(0),
    )
    assert pam_upper >= 0
    exact_lower = F(3, 2) - cosine_upper / sinc_lower - pam_upper / sinc_lower ** 2
    floor_numerator = exact_lower.numerator * SCALE // exact_lower.denominator
    assert floor_numerator == NEW_HW_NUMERATOR
    previous_floor = F(PREVIOUS_HW_NUMERATOR, SCALE)
    new_floor = F(NEW_HW_NUMERATOR, SCALE)
    assert previous_floor < new_floor <= exact_lower < new_floor + F(1, SCALE)

    return {
        "arithmetic": "fractions.Fraction; all asserted comparisons are exact",
        "lean_module": "GramDefect20261015.SharpWindow",
        "lean_theorem": "GramDefect20261015.Window.HW_ge",
        "theta_square": "1/2",
        "cosine_terms": 17,
        "cosine_degree": 32,
        "sinc_terms": 18,
        "sinc_degree": 34,
        "cosine_upper": ratio(cosine_upper),
        "sinc_lower": ratio(sinc_lower),
        "pi_upper": ratio(pi_upper),
        "pam_upper": ratio(pam_upper),
        "exact_window_lower": ratio(exact_lower),
        "exact_window_lower_decimal": decimal(exact_lower),
        "new_floor_numerator": NEW_HW_NUMERATOR,
        "previous_floor_numerator": PREVIOUS_HW_NUMERATOR,
        "floor_denominator": SCALE,
        "new_floor_decimal": decimal(new_floor),
        "strict_floor_gain": ratio(new_floor - previous_floor),
        "strict_floor_gain_decimal": decimal(new_floor - previous_floor),
        "all_exact_checks_passed": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional JSON audit destination")
    args = parser.parse_args()
    result = json.dumps(compute(), indent=2) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(result, encoding="utf-8", newline="\n")
    print(result, end="")


if __name__ == "__main__":
    main()
