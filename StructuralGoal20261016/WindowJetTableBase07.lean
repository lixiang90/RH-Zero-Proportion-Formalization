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
theorem base_29_false : ∀ r ≤ 23, Holds (Base 29 false r) (b r (baseZ 29 false)) := by
 apply b_table_sound E (Base 29 false) e_sound (baseZI_sound 29 false)
   (base_trig_sound 29 false).1 (base_trig_sound 29 false).2
   (base_guard ⟨29,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 29 false) (baseSI 29 false) (baseCI 29) (Base 29 false r) r)
       (Base 29 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_29_false

theorem base_29_true : ∀ r ≤ 23, Holds (Base 29 true r) (b r (baseZ 29 true)) := by
 apply b_table_sound E (Base 29 true) e_sound (baseZI_sound 29 true)
   (base_trig_sound 29 true).1 (base_trig_sound 29 true).2
   (base_guard ⟨29,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 29 true) (baseSI 29 true) (baseCI 29) (Base 29 true r) r)
       (Base 29 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_29_true

theorem base_30_false : ∀ r ≤ 23, Holds (Base 30 false r) (b r (baseZ 30 false)) := by
 apply b_table_sound E (Base 30 false) e_sound (baseZI_sound 30 false)
   (base_trig_sound 30 false).1 (base_trig_sound 30 false).2
   (base_guard ⟨30,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 30 false) (baseSI 30 false) (baseCI 30) (Base 30 false r) r)
       (Base 30 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_30_false

theorem base_30_true : ∀ r ≤ 23, Holds (Base 30 true r) (b r (baseZ 30 true)) := by
 apply b_table_sound E (Base 30 true) e_sound (baseZI_sound 30 true)
   (base_trig_sound 30 true).1 (base_trig_sound 30 true).2
   (base_guard ⟨30,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 30 true) (baseSI 30 true) (baseCI 30) (Base 30 true r) r)
       (Base 30 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_30_true

theorem base_31_false : ∀ r ≤ 23, Holds (Base 31 false r) (b r (baseZ 31 false)) := by
 apply b_table_sound E (Base 31 false) e_sound (baseZI_sound 31 false)
   (base_trig_sound 31 false).1 (base_trig_sound 31 false).2
   (base_guard ⟨31,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 31 false) (baseSI 31 false) (baseCI 31) (Base 31 false r) r)
       (Base 31 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_31_false

theorem base_31_true : ∀ r ≤ 23, Holds (Base 31 true r) (b r (baseZ 31 true)) := by
 apply b_table_sound E (Base 31 true) e_sound (baseZI_sound 31 true)
   (base_trig_sound 31 true).1 (base_trig_sound 31 true).2
   (base_guard ⟨31,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 31 true) (baseSI 31 true) (baseCI 31) (Base 31 true r) r)
       (Base 31 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_31_true

theorem base_32_false : ∀ r ≤ 23, Holds (Base 32 false r) (b r (baseZ 32 false)) := by
 apply b_table_sound E (Base 32 false) e_sound (baseZI_sound 32 false)
   (base_trig_sound 32 false).1 (base_trig_sound 32 false).2
   (base_guard ⟨32,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 32 false) (baseSI 32 false) (baseCI 32) (Base 32 false r) r)
       (Base 32 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_32_false

theorem base_32_true : ∀ r ≤ 23, Holds (Base 32 true r) (b r (baseZ 32 true)) := by
 apply b_table_sound E (Base 32 true) e_sound (baseZI_sound 32 true)
   (base_trig_sound 32 true).1 (base_trig_sound 32 true).2
   (base_guard ⟨32,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 32 true) (baseSI 32 true) (baseCI 32) (Base 32 true r) r)
       (Base 32 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_32_true

end StructuralGoal20261016.WindowJetTableBounds
end
