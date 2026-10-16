/- SPDX-License-Identifier: Apache-2.0
A complete actual lifted graph/KKT pilot on one frozen difference cell.
All scalar, facet and finite aggregate premises are discharged. This local
exclusion is not a complete global cover or an unconditional zero record.
-/
import StructuralGoal20261016.WindowLiftedPilotAtomsAll
import StructuralGoal20261016.WindowLiftedPilotAggregate
set_option Elab.async false
set_option maxHeartbeats 0
namespace StructuralGoal20261016.WindowLiftedPilot
open WindowLiftedPilotData
theorem checked : WindowLiftedKKT.check (123/128) cell atoms weights minimum edges = true := by
 unfold WindowLiftedKKT.check
 simp only [Bool.and_eq_true]
 constructor
 · simpa only [decide_eq_true_eq] using WindowLiftedPilotAtomsAll.checked
 · exact WindowLiftedPilotAggregate.farkas_checked
theorem exclude {g : Fin 9 → ℝ}
 (hg : WindowMinimizerCover.Relevant ((123:ℝ)/128) g)
 (hcell : WindowDifferenceCell.Contains cell g) : False := by
 apply WindowLiftedKKT.exclude atoms weights minimum edges checked
 · simpa only [Rat.cast_div,Rat.cast_ofNat] using hg
 · exact hcell
set_option pp.fullNames true
#print axioms checked
#print axioms exclude
end StructuralGoal20261016.WindowLiftedPilot
