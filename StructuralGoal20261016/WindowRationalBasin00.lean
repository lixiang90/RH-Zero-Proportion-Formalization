/- SPDX-License-Identifier: Apache-2.0
Pure rational diagonal certificate and actual coherent-basin floor 0.
-/
import StructuralGoal20261016.WindowRationalBasinData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowRationalBasins
open WindowGramRational WindowRationalBasinData
theorem check00 : check (basin 0) (221/25000) = true := by decide +kernel
theorem actual00 (g : Fin 9 → ℝ) (hg : Region (basin 0) g) :
 (221:ℝ)/25000 ≤ WindowGapEnergy.Fw24 g := by
 convert WindowGramRational.actual check00 g hg using 1 <;> norm_num
set_option pp.fullNames true
#print axioms check00
#print axioms actual00
end StructuralGoal20261016.WindowRationalBasins
end
