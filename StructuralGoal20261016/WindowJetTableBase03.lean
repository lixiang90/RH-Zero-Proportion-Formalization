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
theorem base_13_false : ∀ r ≤ 23, Holds (Base 13 false r) (b r (baseZ 13 false)) := by
 apply b_table_sound E (Base 13 false) e_sound (baseZI_sound 13 false)
   (base_trig_sound 13 false).1 (base_trig_sound 13 false).2
   (base_guard ⟨13,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 13 false) (baseSI 13 false) (baseCI 13) (Base 13 false r) r)
       (Base 13 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_13_false

theorem base_13_true : ∀ r ≤ 23, Holds (Base 13 true r) (b r (baseZ 13 true)) := by
 apply b_table_sound E (Base 13 true) e_sound (baseZI_sound 13 true)
   (base_trig_sound 13 true).1 (base_trig_sound 13 true).2
   (base_guard ⟨13,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 13 true) (baseSI 13 true) (baseCI 13) (Base 13 true r) r)
       (Base 13 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_13_true

theorem base_14_false : ∀ r ≤ 23, Holds (Base 14 false r) (b r (baseZ 14 false)) := by
 apply b_table_sound E (Base 14 false) e_sound (baseZI_sound 14 false)
   (base_trig_sound 14 false).1 (base_trig_sound 14 false).2
   (base_guard ⟨14,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 14 false) (baseSI 14 false) (baseCI 14) (Base 14 false r) r)
       (Base 14 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_14_false

theorem base_14_true : ∀ r ≤ 23, Holds (Base 14 true r) (b r (baseZ 14 true)) := by
 apply b_table_sound E (Base 14 true) e_sound (baseZI_sound 14 true)
   (base_trig_sound 14 true).1 (base_trig_sound 14 true).2
   (base_guard ⟨14,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 14 true) (baseSI 14 true) (baseCI 14) (Base 14 true r) r)
       (Base 14 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_14_true

theorem base_15_false : ∀ r ≤ 23, Holds (Base 15 false r) (b r (baseZ 15 false)) := by
 apply b_table_sound E (Base 15 false) e_sound (baseZI_sound 15 false)
   (base_trig_sound 15 false).1 (base_trig_sound 15 false).2
   (base_guard ⟨15,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 15 false) (baseSI 15 false) (baseCI 15) (Base 15 false r) r)
       (Base 15 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_15_false

theorem base_15_true : ∀ r ≤ 23, Holds (Base 15 true r) (b r (baseZ 15 true)) := by
 apply b_table_sound E (Base 15 true) e_sound (baseZI_sound 15 true)
   (base_trig_sound 15 true).1 (base_trig_sound 15 true).2
   (base_guard ⟨15,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 15 true) (baseSI 15 true) (baseCI 15) (Base 15 true r) r)
       (Base 15 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_15_true

theorem base_16_false : ∀ r ≤ 23, Holds (Base 16 false r) (b r (baseZ 16 false)) := by
 apply b_table_sound E (Base 16 false) e_sound (baseZI_sound 16 false)
   (base_trig_sound 16 false).1 (base_trig_sound 16 false).2
   (base_guard ⟨16,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 16 false) (baseSI 16 false) (baseCI 16) (Base 16 false r) r)
       (Base 16 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_16_false

theorem base_16_true : ∀ r ≤ 23, Holds (Base 16 true r) (b r (baseZ 16 true)) := by
 apply b_table_sound E (Base 16 true) e_sound (baseZI_sound 16 true)
   (base_trig_sound 16 true).1 (base_trig_sound 16 true).2
   (base_guard ⟨16,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 16 true) (baseSI 16 true) (baseCI 16) (Base 16 true r) r)
       (Base 16 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_16_true

end StructuralGoal20261016.WindowJetTableBounds
end
