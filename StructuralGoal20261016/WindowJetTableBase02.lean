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
theorem base_9_false : ∀ r ≤ 23, Holds (Base 9 false r) (b r (baseZ 9 false)) := by
 apply b_table_sound E (Base 9 false) e_sound (baseZI_sound 9 false)
   (base_trig_sound 9 false).1 (base_trig_sound 9 false).2
   (base_guard ⟨9,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 9 false) (baseSI 9 false) (baseCI 9) (Base 9 false r) r)
       (Base 9 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_9_false

theorem base_9_true : ∀ r ≤ 23, Holds (Base 9 true r) (b r (baseZ 9 true)) := by
 apply b_table_sound E (Base 9 true) e_sound (baseZI_sound 9 true)
   (base_trig_sound 9 true).1 (base_trig_sound 9 true).2
   (base_guard ⟨9,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 9 true) (baseSI 9 true) (baseCI 9) (Base 9 true r) r)
       (Base 9 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_9_true

theorem base_10_false : ∀ r ≤ 23, Holds (Base 10 false r) (b r (baseZ 10 false)) := by
 apply b_table_sound E (Base 10 false) e_sound (baseZI_sound 10 false)
   (base_trig_sound 10 false).1 (base_trig_sound 10 false).2
   (base_guard ⟨10,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 10 false) (baseSI 10 false) (baseCI 10) (Base 10 false r) r)
       (Base 10 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_10_false

theorem base_10_true : ∀ r ≤ 23, Holds (Base 10 true r) (b r (baseZ 10 true)) := by
 apply b_table_sound E (Base 10 true) e_sound (baseZI_sound 10 true)
   (base_trig_sound 10 true).1 (base_trig_sound 10 true).2
   (base_guard ⟨10,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 10 true) (baseSI 10 true) (baseCI 10) (Base 10 true r) r)
       (Base 10 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_10_true

theorem base_11_false : ∀ r ≤ 23, Holds (Base 11 false r) (b r (baseZ 11 false)) := by
 apply b_table_sound E (Base 11 false) e_sound (baseZI_sound 11 false)
   (base_trig_sound 11 false).1 (base_trig_sound 11 false).2
   (base_guard ⟨11,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 11 false) (baseSI 11 false) (baseCI 11) (Base 11 false r) r)
       (Base 11 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_11_false

theorem base_11_true : ∀ r ≤ 23, Holds (Base 11 true r) (b r (baseZ 11 true)) := by
 apply b_table_sound E (Base 11 true) e_sound (baseZI_sound 11 true)
   (base_trig_sound 11 true).1 (base_trig_sound 11 true).2
   (base_guard ⟨11,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 11 true) (baseSI 11 true) (baseCI 11) (Base 11 true r) r)
       (Base 11 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_11_true

theorem base_12_false : ∀ r ≤ 23, Holds (Base 12 false r) (b r (baseZ 12 false)) := by
 apply b_table_sound E (Base 12 false) e_sound (baseZI_sound 12 false)
   (base_trig_sound 12 false).1 (base_trig_sound 12 false).2
   (base_guard ⟨12,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 12 false) (baseSI 12 false) (baseCI 12) (Base 12 false r) r)
       (Base 12 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_12_false

theorem base_12_true : ∀ r ≤ 23, Holds (Base 12 true r) (b r (baseZ 12 true)) := by
 apply b_table_sound E (Base 12 true) e_sound (baseZI_sound 12 true)
   (base_trig_sound 12 true).1 (base_trig_sound 12 true).2
   (base_guard ⟨12,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 12 true) (baseSI 12 true) (baseCI 12) (Base 12 true r) r)
       (Base 12 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_12_true

end StructuralGoal20261016.WindowJetTableBounds
end
