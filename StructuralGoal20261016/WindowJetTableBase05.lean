/- SPDX-License-Identifier: Apache-2.0
Stepwise fixed-grid interval checks for actual normalized sinc moments.
-/
import StructuralGoal20261016.WindowJetTablePilot
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowJetTableBounds
set_option pp.fullNames true
open WindowRationalInterval WindowNormalizedJets WindowIntegerJetRecipe
open WindowIntegerKernelRecipe WindowJetTableConsumer WindowJetTableData WindowJetTablePilot
theorem base_21_false : ∀ r ≤ 23, Holds (Base 21 false r) (b r (baseZ 21 false)) := by
 apply b_table_sound E (Base 21 false) e_sound (baseZI_sound 21 false)
   (base_trig_sound 21 false).1 (base_trig_sound 21 false).2
   (base_guard ⟨21,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 21 false) (baseSI 21 false) (baseCI 21) (Base 21 false r) r)
       (Base 21 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_21_false

theorem base_21_true : ∀ r ≤ 23, Holds (Base 21 true r) (b r (baseZ 21 true)) := by
 apply b_table_sound E (Base 21 true) e_sound (baseZI_sound 21 true)
   (base_trig_sound 21 true).1 (base_trig_sound 21 true).2
   (base_guard ⟨21,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 21 true) (baseSI 21 true) (baseCI 21) (Base 21 true r) r)
       (Base 21 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_21_true

theorem base_22_false : ∀ r ≤ 23, Holds (Base 22 false r) (b r (baseZ 22 false)) := by
 apply b_table_sound E (Base 22 false) e_sound (baseZI_sound 22 false)
   (base_trig_sound 22 false).1 (base_trig_sound 22 false).2
   (base_guard ⟨22,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 22 false) (baseSI 22 false) (baseCI 22) (Base 22 false r) r)
       (Base 22 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_22_false

theorem base_22_true : ∀ r ≤ 23, Holds (Base 22 true r) (b r (baseZ 22 true)) := by
 apply b_table_sound E (Base 22 true) e_sound (baseZI_sound 22 true)
   (base_trig_sound 22 true).1 (base_trig_sound 22 true).2
   (base_guard ⟨22,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 22 true) (baseSI 22 true) (baseCI 22) (Base 22 true r) r)
       (Base 22 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_22_true

theorem base_23_false : ∀ r ≤ 23, Holds (Base 23 false r) (b r (baseZ 23 false)) := by
 apply b_table_sound E (Base 23 false) e_sound (baseZI_sound 23 false)
   (base_trig_sound 23 false).1 (base_trig_sound 23 false).2
   (base_guard ⟨23,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 23 false) (baseSI 23 false) (baseCI 23) (Base 23 false r) r)
       (Base 23 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_23_false

theorem base_23_true : ∀ r ≤ 23, Holds (Base 23 true r) (b r (baseZ 23 true)) := by
 apply b_table_sound E (Base 23 true) e_sound (baseZI_sound 23 true)
   (base_trig_sound 23 true).1 (base_trig_sound 23 true).2
   (base_guard ⟨23,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 23 true) (baseSI 23 true) (baseCI 23) (Base 23 true r) r)
       (Base 23 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_23_true

theorem base_24_false : ∀ r ≤ 23, Holds (Base 24 false r) (b r (baseZ 24 false)) := by
 apply b_table_sound E (Base 24 false) e_sound (baseZI_sound 24 false)
   (base_trig_sound 24 false).1 (base_trig_sound 24 false).2
   (base_guard ⟨24,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 24 false) (baseSI 24 false) (baseCI 24) (Base 24 false r) r)
       (Base 24 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_24_false

theorem base_24_true : ∀ r ≤ 23, Holds (Base 24 true r) (b r (baseZ 24 true)) := by
 apply b_table_sound E (Base 24 true) e_sound (baseZI_sound 24 true)
   (base_trig_sound 24 true).1 (base_trig_sound 24 true).2
   (base_guard ⟨24,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 24 true) (baseSI 24 true) (baseCI 24) (Base 24 true r) r)
       (Base 24 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_24_true

end StructuralGoal20261016.WindowJetTableBounds
end
