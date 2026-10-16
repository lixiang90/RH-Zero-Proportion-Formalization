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
theorem base_17_false : ∀ r ≤ 23, Holds (Base 17 false r) (b r (baseZ 17 false)) := by
 apply b_table_sound E (Base 17 false) e_sound (baseZI_sound 17 false)
   (base_trig_sound 17 false).1 (base_trig_sound 17 false).2
   (base_guard ⟨17,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 17 false) (baseSI 17 false) (baseCI 17) (Base 17 false r) r)
       (Base 17 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_17_false

theorem base_17_true : ∀ r ≤ 23, Holds (Base 17 true r) (b r (baseZ 17 true)) := by
 apply b_table_sound E (Base 17 true) e_sound (baseZI_sound 17 true)
   (base_trig_sound 17 true).1 (base_trig_sound 17 true).2
   (base_guard ⟨17,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 17 true) (baseSI 17 true) (baseCI 17) (Base 17 true r) r)
       (Base 17 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_17_true

theorem base_18_false : ∀ r ≤ 23, Holds (Base 18 false r) (b r (baseZ 18 false)) := by
 apply b_table_sound E (Base 18 false) e_sound (baseZI_sound 18 false)
   (base_trig_sound 18 false).1 (base_trig_sound 18 false).2
   (base_guard ⟨18,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 18 false) (baseSI 18 false) (baseCI 18) (Base 18 false r) r)
       (Base 18 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_18_false

theorem base_18_true : ∀ r ≤ 23, Holds (Base 18 true r) (b r (baseZ 18 true)) := by
 apply b_table_sound E (Base 18 true) e_sound (baseZI_sound 18 true)
   (base_trig_sound 18 true).1 (base_trig_sound 18 true).2
   (base_guard ⟨18,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 18 true) (baseSI 18 true) (baseCI 18) (Base 18 true r) r)
       (Base 18 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_18_true

theorem base_19_false : ∀ r ≤ 23, Holds (Base 19 false r) (b r (baseZ 19 false)) := by
 apply b_table_sound E (Base 19 false) e_sound (baseZI_sound 19 false)
   (base_trig_sound 19 false).1 (base_trig_sound 19 false).2
   (base_guard ⟨19,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 19 false) (baseSI 19 false) (baseCI 19) (Base 19 false r) r)
       (Base 19 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_19_false

theorem base_19_true : ∀ r ≤ 23, Holds (Base 19 true r) (b r (baseZ 19 true)) := by
 apply b_table_sound E (Base 19 true) e_sound (baseZI_sound 19 true)
   (base_trig_sound 19 true).1 (base_trig_sound 19 true).2
   (base_guard ⟨19,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 19 true) (baseSI 19 true) (baseCI 19) (Base 19 true r) r)
       (Base 19 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_19_true

theorem base_20_false : ∀ r ≤ 23, Holds (Base 20 false r) (b r (baseZ 20 false)) := by
 apply b_table_sound E (Base 20 false) e_sound (baseZI_sound 20 false)
   (base_trig_sound 20 false).1 (base_trig_sound 20 false).2
   (base_guard ⟨20,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 20 false) (baseSI 20 false) (baseCI 20) (Base 20 false r) r)
       (Base 20 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_20_false

theorem base_20_true : ∀ r ≤ 23, Holds (Base 20 true r) (b r (baseZ 20 true)) := by
 apply b_table_sound E (Base 20 true) e_sound (baseZI_sound 20 true)
   (base_trig_sound 20 true).1 (base_trig_sound 20 true).2
   (base_guard ⟨20,by decide⟩ true)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 20 true) (baseSI 20 true) (baseCI 20) (Base 20 true r) r)
       (Base 20 true ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms base_20_true

end StructuralGoal20261016.WindowJetTableBounds
end
