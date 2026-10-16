"""Generate bounded ordinary-kernel checkpoints for all separated grid cells.

The data and oracle endpoints are unchanged. Each proof checks at most 32
cells, so the first block can be timed before dispatching the remaining
blocks. This script does not invoke Lean or change either dispatch queue.
"""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).parent
COUNT = 1987
SIZE = 32
GROUPS = (COUNT + SIZE - 1) // SIZE
modules = []

for g in range(GROUPS):
    name = f"WindowGridChecks{g:02}"
    source = f"""/- SPDX-License-Identifier: Apache-2.0
Actual whole-cell derivative checks for separated grid cells
{61+g*SIZE}..{min(2047,60+(g+1)*SIZE)}.
-/
import StructuralGoal20261016.WindowGridCertificateData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowGridChecks
open WindowGridCertificate WindowGridCertificateData
theorem checks{g:02} : ∀ j : Fin {SIZE}, {g}*{SIZE}+(j:ℕ) < {COUNT} →
 check (61+{g}*{SIZE}+(j:ℕ)) (row ({g}*{SIZE}+(j:ℕ))) = true := by decide +kernel
set_option pp.fullNames true
#print axioms checks{g:02}
end StructuralGoal20261016.WindowGridChecks
"""
    (ROOT / f"StructuralGoal20261016/{name}.lean").write_text(
        source, encoding="utf8", newline="\n"
    )
    modules.append(f"StructuralGoal20261016.{name}")

source = """/- SPDX-License-Identifier: Apache-2.0
All original quantized derivative and third-derivative bounds on the
separated domain. Cell k is [k/64,(k+1)/64]; only k>=61 is consumed by
the separation 123/128. No endpoint constants are replaced.
-/
"""
source += "\n".join(f"import {m}" for m in modules)
source += "\nimport StructuralGoal20261016.WindowGridRange"
source += f"""
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowGridAll
open WindowGridCertificate WindowGridCertificateData WindowGridChecks

theorem checks : ∀ g : Fin {GROUPS}, ∀ j : Fin {SIZE}, (g:ℕ)*{SIZE}+(j:ℕ) < {COUNT} →
 check (61+(g:ℕ)*{SIZE}+(j:ℕ)) (row ((g:ℕ)*{SIZE}+(j:ℕ))) = true := by
 intro g
 fin_cases g
"""
source += "\n".join(f" · exact checks{g:02}" for g in range(GROUPS))
source += f"""

theorem valid_index (i : ℕ) (hi : i < {COUNT}) : Valid (61+i) (row i) := by
 have hg : i/{SIZE} < {GROUPS} := by omega
 have hj : i%{SIZE} < {SIZE} := Nat.mod_lt i (by decide)
 have he : i/{SIZE}*{SIZE}+i%{SIZE} = i := by omega
 have hc := checks ⟨i/{SIZE},hg⟩ ⟨i%{SIZE},hj⟩
   (by change i/{SIZE}*{SIZE}+i%{SIZE} < {COUNT}; omega)
 change check (61+i/{SIZE}*{SIZE}+i%{SIZE}) (row (i/{SIZE}*{SIZE}+i%{SIZE})) = true at hc
 have he' : 61+i/{SIZE}*{SIZE}+i%{SIZE} = 61+i := by omega
 rw [he,he'] at hc
 exact WindowGridCertificate.sound hc

theorem valid (k : ℕ) (hk0 : 61 ≤ k) (hk1 : k < 2048) : Valid k (row (k-61)) := by
 have h := valid_index (k-61) (by omega)
 have he : 61+(k-61) = k := by omega
 rwa [he] at h

theorem derivative (k : ℕ) (hk0 : 61 ≤ k) (hk1 : k < 2048)
 {{x : ℝ}} (hx : x ∈ Icc (left k:ℝ) (right k:ℝ)) :
 ((row (k-61)).lower:ℝ)/10^15 ≤ WindowGapEnergy.w1 x ∧
 WindowGapEnergy.w1 x ≤ ((row (k-61)).upper:ℝ)/10^15 :=
 ⟨(valid k hk0 hk1 x hx).1,(valid k hk0 hk1 x hx).2.1⟩

theorem third (k : ℕ) (hk0 : 61 ≤ k) (hk1 : k < 2048)
 {{x : ℝ}} (hx : x ∈ Icc (left k:ℝ) (right k:ℝ)) :
 |iteratedDeriv 3 WindowScalarMinorant.f x| ≤ ((row (k-61)).third:ℝ)/10^15 :=
 (valid k hk0 hk1 x hx).2.2

theorem gridSound : WindowGridRange.GridSound := fun k hk0 hk1 => valid k hk0 hk1

theorem range_sound {{k0 k1 : ℕ}} {{a b L U M : ℚ}}
 (hc : WindowGridRange.check k0 k1 a b L U M = true)
 {{x : ℝ}} (hx : x ∈ Icc (a:ℝ) b) :
 (L:ℝ) ≤ WindowGapEnergy.w1 x ∧ WindowGapEnergy.w1 x ≤ (U:ℝ) ∧
 |iteratedDeriv 3 WindowScalarMinorant.f x| ≤ (M:ℝ) :=
 WindowGridRange.sound gridSound hc hx

set_option pp.fullNames true
#print axioms valid
#print axioms derivative
#print axioms third
#print axioms range_sound
end StructuralGoal20261016.WindowGridAll
end
"""
(ROOT / "StructuralGoal20261016/WindowGridAll.lean").write_text(
    source, encoding="utf8", newline="\n"
)
modules.append("StructuralGoal20261016.WindowGridAll")
(HERE / "window_grid_check_modules.json").write_text(
    json.dumps(modules, indent=2) + "\n", encoding="utf8"
)
print(json.dumps({"cells": COUNT, "block_size": SIZE, "blocks": GROUPS,
                  "source_bytes": sum((ROOT / (m.replace('.', '/')+'.lean')).stat().st_size
                                      for m in modules),
                  "ordinary_Lean_proven": False}))
