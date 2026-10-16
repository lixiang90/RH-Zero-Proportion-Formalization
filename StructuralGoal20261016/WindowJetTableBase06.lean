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
theorem base_25_false : ∀ r ≤ 23, Holds (Base 25 false r) (b r (baseZ 25 false)) := by
 apply b_table_sound E (Base 25 false) e_sound (baseZI_sound 25 false)
   (base_trig_sound 25 false).1 (base_trig_sound 25 false).2
   (base_guard ⟨25,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 25 false) (baseSI 25 false) (baseCI 25) (Base 25 false r) r)
       (Base 25 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_25_false

theorem base_25_true : ∀ r ≤ 23, Holds (Base 25 true r) (b r (baseZ 25 true)) := by
 apply b_table_sound E (Base 25 true) e_sound (baseZI_sound 25 true)
   (base_trig_sound 25 true).1 (base_trig_sound 25 true).2
   (base_guard ⟨25,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 25 true) (baseSI 25 true) (baseCI 25) (Base 25 true r) r)
       (Base 25 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_25_true

theorem base_26_false : ∀ r ≤ 23, Holds (Base 26 false r) (b r (baseZ 26 false)) := by
 apply b_table_sound E (Base 26 false) e_sound (baseZI_sound 26 false)
   (base_trig_sound 26 false).1 (base_trig_sound 26 false).2
   (base_guard ⟨26,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 26 false) (baseSI 26 false) (baseCI 26) (Base 26 false r) r)
       (Base 26 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_26_false

theorem base_26_true : ∀ r ≤ 23, Holds (Base 26 true r) (b r (baseZ 26 true)) := by
 apply b_table_sound E (Base 26 true) e_sound (baseZI_sound 26 true)
   (base_trig_sound 26 true).1 (base_trig_sound 26 true).2
   (base_guard ⟨26,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 26 true) (baseSI 26 true) (baseCI 26) (Base 26 true r) r)
       (Base 26 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_26_true

theorem base_27_false : ∀ r ≤ 23, Holds (Base 27 false r) (b r (baseZ 27 false)) := by
 apply b_table_sound E (Base 27 false) e_sound (baseZI_sound 27 false)
   (base_trig_sound 27 false).1 (base_trig_sound 27 false).2
   (base_guard ⟨27,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 27 false) (baseSI 27 false) (baseCI 27) (Base 27 false r) r)
       (Base 27 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_27_false

theorem base_27_true : ∀ r ≤ 23, Holds (Base 27 true r) (b r (baseZ 27 true)) := by
 apply b_table_sound E (Base 27 true) e_sound (baseZI_sound 27 true)
   (base_trig_sound 27 true).1 (base_trig_sound 27 true).2
   (base_guard ⟨27,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 27 true) (baseSI 27 true) (baseCI 27) (Base 27 true r) r)
       (Base 27 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_27_true

theorem base_28_false : ∀ r ≤ 23, Holds (Base 28 false r) (b r (baseZ 28 false)) := by
 apply b_table_sound E (Base 28 false) e_sound (baseZI_sound 28 false)
   (base_trig_sound 28 false).1 (base_trig_sound 28 false).2
   (base_guard ⟨28,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 28 false) (baseSI 28 false) (baseCI 28) (Base 28 false r) r)
       (Base 28 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_28_false

theorem base_28_true : ∀ r ≤ 23, Holds (Base 28 true r) (b r (baseZ 28 true)) := by
 apply b_table_sound E (Base 28 true) e_sound (baseZI_sound 28 true)
   (base_trig_sound 28 true).1 (base_trig_sound 28 true).2
   (base_guard ⟨28,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 28 true) (baseSI 28 true) (baseCI 28) (Base 28 true r) r)
       (Base 28 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_28_true

end StructuralGoal20261016.WindowJetTableBounds
end
