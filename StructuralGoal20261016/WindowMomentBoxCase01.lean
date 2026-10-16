/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentBoxData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowMomentBoxCase01
open WindowMomentBox WindowMomentBoxData WindowMomentEnergyData
theorem checked : check cell1 box1 = true := by decide +kernel
theorem bounds {g : Fin 9 → ℝ} (hg : WindowDifferenceCell.Contains cell1 g) :
 ∀ i, (lower box1 i:ℝ) ≤ actual box1 g i ∧ actual box1 g i ≤ (upper box1 i:ℝ) :=
 sound checked hg
set_option pp.fullNames true
#print axioms checked
#print axioms bounds
end StructuralGoal20261016.WindowMomentBoxCase01
end
