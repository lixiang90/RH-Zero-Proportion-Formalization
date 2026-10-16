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
theorem base_5_false : ∀ r ≤ 23, Holds (Base 5 false r) (b r (baseZ 5 false)) := by
 apply b_table_sound E (Base 5 false) e_sound (baseZI_sound 5 false)
   (base_trig_sound 5 false).1 (base_trig_sound 5 false).2
   (base_guard ⟨5,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 5 false) (baseSI 5 false) (baseCI 5) (Base 5 false r) r)
       (Base 5 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_5_false

theorem base_5_true : ∀ r ≤ 23, Holds (Base 5 true r) (b r (baseZ 5 true)) := by
 apply b_table_sound E (Base 5 true) e_sound (baseZI_sound 5 true)
   (base_trig_sound 5 true).1 (base_trig_sound 5 true).2
   (base_guard ⟨5,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 5 true) (baseSI 5 true) (baseCI 5) (Base 5 true r) r)
       (Base 5 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_5_true

theorem base_6_false : ∀ r ≤ 23, Holds (Base 6 false r) (b r (baseZ 6 false)) := by
 apply b_table_sound E (Base 6 false) e_sound (baseZI_sound 6 false)
   (base_trig_sound 6 false).1 (base_trig_sound 6 false).2
   (base_guard ⟨6,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 6 false) (baseSI 6 false) (baseCI 6) (Base 6 false r) r)
       (Base 6 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_6_false

theorem base_6_true : ∀ r ≤ 23, Holds (Base 6 true r) (b r (baseZ 6 true)) := by
 apply b_table_sound E (Base 6 true) e_sound (baseZI_sound 6 true)
   (base_trig_sound 6 true).1 (base_trig_sound 6 true).2
   (base_guard ⟨6,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 6 true) (baseSI 6 true) (baseCI 6) (Base 6 true r) r)
       (Base 6 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_6_true

theorem base_7_false : ∀ r ≤ 23, Holds (Base 7 false r) (b r (baseZ 7 false)) := by
 apply b_table_sound E (Base 7 false) e_sound (baseZI_sound 7 false)
   (base_trig_sound 7 false).1 (base_trig_sound 7 false).2
   (base_guard ⟨7,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 7 false) (baseSI 7 false) (baseCI 7) (Base 7 false r) r)
       (Base 7 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_7_false

theorem base_7_true : ∀ r ≤ 23, Holds (Base 7 true r) (b r (baseZ 7 true)) := by
 apply b_table_sound E (Base 7 true) e_sound (baseZI_sound 7 true)
   (base_trig_sound 7 true).1 (base_trig_sound 7 true).2
   (base_guard ⟨7,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 7 true) (baseSI 7 true) (baseCI 7) (Base 7 true r) r)
       (Base 7 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_7_true

theorem base_8_false : ∀ r ≤ 23, Holds (Base 8 false r) (b r (baseZ 8 false)) := by
 apply b_table_sound E (Base 8 false) e_sound (baseZI_sound 8 false)
   (base_trig_sound 8 false).1 (base_trig_sound 8 false).2
   (base_guard ⟨8,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 8 false) (baseSI 8 false) (baseCI 8) (Base 8 false r) r)
       (Base 8 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_8_false

theorem base_8_true : ∀ r ≤ 23, Holds (Base 8 true r) (b r (baseZ 8 true)) := by
 apply b_table_sound E (Base 8 true) e_sound (baseZI_sound 8 true)
   (base_trig_sound 8 true).1 (base_trig_sound 8 true).2
   (base_guard ⟨8,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 8 true) (baseSI 8 true) (baseCI 8) (Base 8 true r) r)
       (Base 8 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_8_true

end StructuralGoal20261016.WindowJetTableBounds
end
