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
theorem base_1_false : ∀ r ≤ 23, Holds (Base 1 false r) (b r (baseZ 1 false)) := by
 apply b_table_sound E (Base 1 false) e_sound (baseZI_sound 1 false)
   (base_trig_sound 1 false).1 (base_trig_sound 1 false).2
   (base_guard ⟨1,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 1 false) (baseSI 1 false) (baseCI 1) (Base 1 false r) r)
       (Base 1 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_1_false

theorem base_1_true : ∀ r ≤ 23, Holds (Base 1 true r) (b r (baseZ 1 true)) := by
 apply b_table_sound E (Base 1 true) e_sound (baseZI_sound 1 true)
   (base_trig_sound 1 true).1 (base_trig_sound 1 true).2
   (base_guard ⟨1,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 1 true) (baseSI 1 true) (baseCI 1) (Base 1 true r) r)
       (Base 1 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_1_true

theorem base_2_false : ∀ r ≤ 23, Holds (Base 2 false r) (b r (baseZ 2 false)) := by
 apply b_table_sound E (Base 2 false) e_sound (baseZI_sound 2 false)
   (base_trig_sound 2 false).1 (base_trig_sound 2 false).2
   (base_guard ⟨2,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 2 false) (baseSI 2 false) (baseCI 2) (Base 2 false r) r)
       (Base 2 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_2_false

theorem base_2_true : ∀ r ≤ 23, Holds (Base 2 true r) (b r (baseZ 2 true)) := by
 apply b_table_sound E (Base 2 true) e_sound (baseZI_sound 2 true)
   (base_trig_sound 2 true).1 (base_trig_sound 2 true).2
   (base_guard ⟨2,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 2 true) (baseSI 2 true) (baseCI 2) (Base 2 true r) r)
       (Base 2 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_2_true

theorem base_3_false : ∀ r ≤ 23, Holds (Base 3 false r) (b r (baseZ 3 false)) := by
 apply b_table_sound E (Base 3 false) e_sound (baseZI_sound 3 false)
   (base_trig_sound 3 false).1 (base_trig_sound 3 false).2
   (base_guard ⟨3,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 3 false) (baseSI 3 false) (baseCI 3) (Base 3 false r) r)
       (Base 3 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_3_false

theorem base_3_true : ∀ r ≤ 23, Holds (Base 3 true r) (b r (baseZ 3 true)) := by
 apply b_table_sound E (Base 3 true) e_sound (baseZI_sound 3 true)
   (base_trig_sound 3 true).1 (base_trig_sound 3 true).2
   (base_guard ⟨3,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 3 true) (baseSI 3 true) (baseCI 3) (Base 3 true r) r)
       (Base 3 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_3_true

theorem base_4_false : ∀ r ≤ 23, Holds (Base 4 false r) (b r (baseZ 4 false)) := by
 apply b_table_sound E (Base 4 false) e_sound (baseZI_sound 4 false)
   (base_trig_sound 4 false).1 (base_trig_sound 4 false).2
   (base_guard ⟨4,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 4 false) (baseSI 4 false) (baseCI 4) (Base 4 false r) r)
       (Base 4 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_4_false

theorem base_4_true : ∀ r ≤ 23, Holds (Base 4 true r) (b r (baseZ 4 true)) := by
 apply b_table_sound E (Base 4 true) e_sound (baseZI_sound 4 true)
   (base_trig_sound 4 true).1 (base_trig_sound 4 true).2
   (base_guard ⟨4,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 4 true) (baseSI 4 true) (baseCI 4) (Base 4 true r) r)
       (Base 4 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_4_true

end StructuralGoal20261016.WindowJetTableBounds
end
