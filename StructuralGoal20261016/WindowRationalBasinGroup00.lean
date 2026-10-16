/- SPDX-License-Identifier: Apache-2.0
Shared-import rational checks for basin indices 1..8.
-/
import StructuralGoal20261016.WindowRationalBasinData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowRationalBasinGroups
open WindowGramRational WindowRationalBasinData
theorem checks00 : ∀ j : Fin 8, 1+0*8+(j:ℕ) < 69 →
 check (basin (1+0*8+(j:ℕ))) (221/25000) = true := by decide +kernel
theorem actual00 (j : Fin 8) (hj : 1+0*8+(j:ℕ) < 69)
 (gaps : Fin 9 → ℝ) (hg : Region (basin (1+0*8+(j:ℕ))) gaps) :
 (221:ℝ)/25000 ≤ WindowGapEnergy.Fw24 gaps := by
 convert WindowGramRational.actual (checks00 j hj) gaps hg using 1 <;> norm_num
set_option pp.fullNames true
#print axioms checks00
#print axioms actual00
end StructuralGoal20261016.WindowRationalBasinGroups
end
