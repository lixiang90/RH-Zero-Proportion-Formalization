"""Compact coherent-basin data and independent rational diagonal checks.

This script emits no Lean claims by itself and invokes no verifier. The
first Lean finite-check module should be timed before dispatching all 69.
"""
from pathlib import Path
from fractions import Fraction as F
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).parent
gram = json.loads((HERE / "cover-newwindow-gram.json").read_bytes())
mapping = json.loads((HERE / "window_anchor_map.json").read_bytes())
ledger = json.loads((ROOT / "research-20261016-followup/window_reweight_rational.json").read_bytes())
terms = [tuple(t) for t in ledger["a_upper"] if t[2]]
weights = [F(w, 10**10) for _, _, w in terms]
pressure = [F(w, 10**10) for w in ledger["b_numerators"]]
floor = F(221, 25000)

def q(x):
    x = F(x)
    return f"({x.numerator}/{x.denominator}:ℚ)"

data = """/- SPDX-License-Identifier: Apache-2.0
Untrusted compact anchor coordinates and scalar-row indices for 69 basins.
-/
import StructuralGoal20261016.WindowGramRational
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowRationalBasinData
open WindowGramRational
def values : List Basin := [
"""
rows = []
margins = []
for basin in gram["results"]:
    anchor = list(map(F, basin["anchor"]))
    scalars = basin["scalar_minorants"]
    ids = [mapping[s["anchor"]] for s in scalars]
    assert len(ids) == len(terms) == 41
    V = [F(s["value_lower"]) - F(s["slope_error_loss"]) for s in scalars]
    S = [F(s["slope"]) for s in scalars]
    A = [F(s["quadratic_coefficient"]) for s in scalars]
    assert all(a >= 0 for a in A)
    assert all(F(s["anchor"]) == sum(anchor[i:j])
               for (i, j, _), s in zip(terms, scalars))
    C = sum(b*x for b, x in zip(pressure, anchor)) + sum(w*v for w, v in zip(weights, V))
    linear = [pressure[r]+sum(w*s for w, s, (i, j, _) in zip(weights, S, terms) if i <= r < j)
              for r in range(9)]
    diagonal = [next(w*a for w, a, (i, j, _) in zip(weights, A, terms) if i == r and j == r+1)
                for r in range(9)]
    assert all(d > 0 for d in diagonal)
    value = C-sum(b*b/(4*d) for b, d in zip(linear, diagonal))
    assert value >= floor
    margins.append(value-floor)
    rows.append("⟨!["+", ".join(q(x) for x in anchor)+"], !["+", ".join(map(str, ids))+"]⟩")
data += ",\n ".join(rows)
data += "]\ndef basin (i : ℕ) : Basin := values.getD i ⟨fun _ => 0,fun _ => 0⟩\n"
data += "end StructuralGoal20261016.WindowRationalBasinData\nend\n"
if "--checks-only" not in sys.argv:
    (ROOT / "StructuralGoal20261016/WindowRationalBasinData.lean").write_text(data, encoding="utf8", newline="\n")

modules = []
for b in range(len(rows)):
    name = f"WindowRationalBasin{b:02}"
    source = f"""/- SPDX-License-Identifier: Apache-2.0
Pure rational diagonal certificate and actual coherent-basin floor {b}.
-/
import StructuralGoal20261016.WindowRationalBasinData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowRationalBasins
open WindowGramRational WindowRationalBasinData
theorem check{b:02} : check (basin {b}) (221/25000) = true := by decide +kernel
theorem actual{b:02} (g : Fin 9 → ℝ) (hg : Region (basin {b}) g) :
 (221:ℝ)/25000 ≤ WindowGapEnergy.Fw24 g := by
 convert WindowGramRational.actual check{b:02} g hg using 1 <;> norm_num
set_option pp.fullNames true
#print axioms check{b:02}
#print axioms actual{b:02}
end StructuralGoal20261016.WindowRationalBasins
end
"""
    (ROOT / f"StructuralGoal20261016/{name}.lean").write_text(source, encoding="utf8", newline="\n")
    modules.append(f"StructuralGoal20261016.{name}")
(HERE / "window_rational_basin_modules.json").write_text(json.dumps(modules, indent=2)+"\n", encoding="utf8")
(HERE / "window_rational_basin_audit.json").write_text(json.dumps({
    "basins": len(rows), "minimum_diagonal_margin": str(min(margins)),
    "scope": __doc__, "ordinary_Lean_proven": False}, indent=2)+"\n", encoding="utf8")
print(json.dumps({"basins": len(rows), "data_bytes": len(data.encode()),
                  "minimum_margin": float(min(margins)), "ordinary_Lean_proven": False}))
