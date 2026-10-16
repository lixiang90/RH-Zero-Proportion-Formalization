/- SPDX-License-Identifier: Apache-2.0
All 69 actual coherent-basin floors from compact rational certificates.
Only actual membership in the selected integer wells is an input.
-/
import StructuralGoal20261016.WindowRationalBasin00
import StructuralGoal20261016.WindowRationalBasinGroup00
import StructuralGoal20261016.WindowRationalBasinGroup01
import StructuralGoal20261016.WindowRationalBasinGroup02
import StructuralGoal20261016.WindowRationalBasinGroup03
import StructuralGoal20261016.WindowRationalBasinGroup04
import StructuralGoal20261016.WindowRationalBasinGroup05
import StructuralGoal20261016.WindowRationalBasinGroup06
import StructuralGoal20261016.WindowRationalBasinGroup07
import StructuralGoal20261016.WindowRationalBasinGroup08
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
namespace StructuralGoal20261016.WindowRationalBasinAll
open WindowGramRational WindowRationalBasinData WindowRationalBasinGroups
theorem group_checks : ∀ g : Fin 9, ∀ j : Fin 8, 1+(g:ℕ)*8+(j:ℕ) < 69 →
 check (basin (1+(g:ℕ)*8+(j:ℕ))) (221/25000) = true := by
 intro g
 fin_cases g
 · exact checks00
 · exact checks01
 · exact checks02
 · exact checks03
 · exact checks04
 · exact checks05
 · exact checks06
 · exact checks07
 · exact checks08

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
