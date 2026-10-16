"""Group the remaining 68 rational basin checks to share import overhead.

Preserves the separate basin-0 checkpoint and the frozen data source. No
Lean process or dispatch queue is started by this generator.
"""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).parent
modules = []
for g in range(9):
    name = f"WindowRationalBasinGroup{g:02}"
    source = f"""/- SPDX-License-Identifier: Apache-2.0
Shared-import rational checks for basin indices {1+8*g}..{min(68,8+8*g)}.
-/
import StructuralGoal20261016.WindowRationalBasinData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowRationalBasinGroups
open WindowGramRational WindowRationalBasinData
theorem checks{g:02} : ∀ j : Fin 8, 1+{g}*8+(j:ℕ) < 69 →
 check (basin (1+{g}*8+(j:ℕ))) (221/25000) = true := by decide +kernel
theorem actual{g:02} (j : Fin 8) (hj : 1+{g}*8+(j:ℕ) < 69)
 (gaps : Fin 9 → ℝ) (hg : Region (basin (1+{g}*8+(j:ℕ))) gaps) :
 (221:ℝ)/25000 ≤ WindowGapEnergy.Fw24 gaps := by
 convert WindowGramRational.actual (checks{g:02} j hj) gaps hg using 1 <;> norm_num
set_option pp.fullNames true
#print axioms checks{g:02}
#print axioms actual{g:02}
end StructuralGoal20261016.WindowRationalBasinGroups
end
"""
    (ROOT / f"StructuralGoal20261016/{name}.lean").write_text(source, encoding="utf8", newline="\n")
    modules.append(f"StructuralGoal20261016.{name}")

source = """/- SPDX-License-Identifier: Apache-2.0
All 69 actual coherent-basin floors from compact rational certificates.
Only actual membership in the selected integer wells is an input.
-/
import StructuralGoal20261016.WindowRationalBasin00
"""
source += "\n".join(f"import {m}" for m in modules)
source += """
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
namespace StructuralGoal20261016.WindowRationalBasinAll
open WindowGramRational WindowRationalBasinData WindowRationalBasinGroups
theorem group_checks : ∀ g : Fin 9, ∀ j : Fin 8, 1+(g:ℕ)*8+(j:ℕ) < 69 →
 check (basin (1+(g:ℕ)*8+(j:ℕ))) (221/25000) = true := by
 intro g
 fin_cases g
"""
source += "\n".join(f" · exact checks{g:02}" for g in range(9))
source += """

theorem checked (i : ℕ) (hi : i < 69) : check (basin i) (221/25000) = true := by
 by_cases hz : i = 0
 · subst i
   exact WindowRationalBasins.check00
 · have hgroup : (i-1)/8 < 9 := by omega
   have hindex : (i-1)%8 < 8 := Nat.mod_lt (i-1) (by decide)
   have he : 1+(i-1)/8*8+(i-1)%8 = i := by omega
   have hc := group_checks ⟨(i-1)/8,hgroup⟩ ⟨(i-1)%8,hindex⟩
     (by change 1+(i-1)/8*8+(i-1)%8 < 69; omega)
   change check (basin (1+(i-1)/8*8+(i-1)%8)) (221/25000) = true at hc
   rwa [he] at hc

theorem actual (i : ℕ) (hi : i < 69) (g : Fin 9 → ℝ) (hg : Region (basin i) g) :
 (221:ℝ)/25000 ≤ WindowGapEnergy.Fw24 g := by
 convert WindowGramRational.actual (checked i hi) g hg using 1 <;> norm_num

set_option pp.fullNames true
#print axioms checked
#print axioms actual
end StructuralGoal20261016.WindowRationalBasinAll
end
"""
(ROOT / "StructuralGoal20261016/WindowRationalBasinAll.lean").write_text(source, encoding="utf8", newline="\n")
modules.append("StructuralGoal20261016.WindowRationalBasinAll")
(HERE / "window_rational_basin_group_modules.json").write_text(json.dumps(modules, indent=2)+"\n", encoding="utf8")
print(json.dumps({"groups": 9, "remaining_basins": 68,
                  "source_bytes": sum((ROOT / (m.replace('.', '/')+'.lean')).stat().st_size
                                      for m in modules),
                  "ordinary_Lean_proven": False}))
