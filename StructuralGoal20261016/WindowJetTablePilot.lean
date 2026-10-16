/- SPDX-License-Identifier: Apache-2.0
Small ordinary-kernel pilot for the fixed-grid stepwise jet tables.
-/
import StructuralGoal20261016.WindowJetTableData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowJetTablePilot
open WindowRationalInterval WindowNormalizedJets WindowIntegerJetRecipe
open WindowIntegerKernelRecipe WindowJetTableConsumer WindowJetTableData
theorem e_sound : ∀ r ≤ 23, Holds (E r) (WindowNormalizedJets.e r) := by
 apply e_table_sound
 · decide +kernel
 · have h : ∀ r : Fin 23, covers (rdiv (rmul (E r) piI) (point ((r:ℕ)+2))) (E ((r:ℕ)+1)) = true := by
     decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
theorem base_one_false : ∀ r ≤ 23, Holds (Base 1 false r) (b r (baseZ 1 false)) := by
 apply b_table_sound E (Base 1 false) e_sound (baseZI_sound 1 false)
   (base_trig_sound 1 false).1 (base_trig_sound 1 false).2 (base_guard ⟨1,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 1 false) (baseSI 1 false) (baseCI 1) (Base 1 false r) r)
       (Base 1 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
set_option pp.fullNames true
#print axioms e_sound
#print axioms base_one_false
end StructuralGoal20261016.WindowJetTablePilot
end
