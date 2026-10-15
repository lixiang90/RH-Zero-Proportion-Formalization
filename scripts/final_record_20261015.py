"""Generate the final exact instantiation, independently of decimal display."""
from pathlib import Path
from fractions import Fraction as Q
from decimal import Decimal, localcontext
import json

ROOT = Path(__file__).resolve().parents[1]
H = Q(6721684105641188747759983512104999330646, 10**40)
C = Q(859538525913875481, 10**20)
B = Q(437688000000, 100000000000000)
PREVIOUS = Q(834739413205148593469931805501689594457,
             1239255769294131601825000000000000000000)
K = (H-B)/(1-C)


def main():
    assert 0 < C < Q(1, 64) and K > PREVIOUS
    old = (ROOT / "GramDefectRecord/Final.lean").read_text(encoding="utf8")
    old = old.replace("GramDefectRecord", "GramDefect20261015")
    old = old.replace("import GramDefect20261015.ScaledCertificate\n", "")
    old = old.replace("Exact refinement of the accepted master-of-puppets4 critical-line bound.\nThe same nine-point objective is checked at a finer rational threshold and\ncombined with a sharper window floor. Every premise is discharged below.",
        "Exact refinement of the accepted ajp88 reweighted nine-point bound.\nThe same certificate tree proves a higher local floor, retaining weights\nand pressures. The window uses alternating cos/sinc polynomials at\ntheta^2 = 1/2. Every analytic and finite premise is discharged below.")
    old = old.replace("672168410564118874775945444401 / 10 ^ 30", "6721684105641188747759983512104999330646 / 10 ^ 40")
    old = old.replace("85638285989 / 10000000000000", "859538525913875481 / 100000000000000000000")
    old = old.replace("436674 / 100000000", "437688000000 / 100000000000000")
    old = old.replace("39282451209654051457408555553 / 58319774788300000000000000000", f"{K.numerator} / {K.denominator}")
    old = old.replace("667801670564118872522651 / 991436171500000000000000", f"{PREVIOUS.numerator} / {PREVIOUS.denominator}")
    old = old.replace("RiemannFailScaled", "RiemannFail")
    old = old.replace("ProportionSharpWindow.HW_ge", "GramDefect20261015.Window.HW_ge")
    (ROOT / "GramDefect20261015/Final.lean").write_text(old, encoding="utf8", newline="\n")
    with localcontext() as ctx:
        ctx.prec = 90
        dec = lambda q: str(Decimal(q.numerator)/Decimal(q.denominator))
        report = {"window_floor": str(H), "local_floor": str(C), "pressure": str(B),
                  "numerator": str(K.numerator), "denominator": str(K.denominator),
                  "proportion_decimal": dec(K), "percentage_decimal": dec(100*K),
                  "previous_record": str(PREVIOUS), "strict_gain": str(K-PREVIOUS),
                  "gain_proportion_decimal": dec(K-PREVIOUS),
                  "gain_percentage_points_decimal": dec(100*(K-PREVIOUS)),
                  "strict_exact_comparison": K > PREVIOUS,
                  "official_website_acceptance": False}
    dest = ROOT / "verification/gram-defect-20261015/exact-score.json"
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(json.dumps(report, indent=2) + "\n", encoding="utf8", newline="\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
