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
theorem cos_56 : ∀ r ≤ 23, Holds (Cos (56:ℤ) r) (b r (Real.pi*((56:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (56:ℤ)) (Z := cosZI (56:ℤ)) (S := point 0) (C := signI (56:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (56:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (56:ℤ)) (point 0) (signI (56:ℤ)) (Cos (56:ℤ) r) r)
       (Cos (56:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_56

end StructuralGoal20261016.WindowJetTableBounds
end
