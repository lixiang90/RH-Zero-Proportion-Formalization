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
theorem cos_8 : ∀ r ≤ 23, Holds (Cos (8:ℤ) r) (b r (Real.pi*((8:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (8:ℤ)) (Z := cosZI (8:ℤ)) (S := point 0) (C := signI (8:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (8:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (8:ℤ)) (point 0) (signI (8:ℤ)) (Cos (8:ℤ) r) r)
       (Cos (8:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_8

theorem cos_9 : ∀ r ≤ 23, Holds (Cos (9:ℤ) r) (b r (Real.pi*((9:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (9:ℤ)) (Z := cosZI (9:ℤ)) (S := point 0) (C := signI (9:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (9:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (9:ℤ)) (point 0) (signI (9:ℤ)) (Cos (9:ℤ) r) r)
       (Cos (9:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_9

theorem cos_10 : ∀ r ≤ 23, Holds (Cos (10:ℤ) r) (b r (Real.pi*((10:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (10:ℤ)) (Z := cosZI (10:ℤ)) (S := point 0) (C := signI (10:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (10:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (10:ℤ)) (point 0) (signI (10:ℤ)) (Cos (10:ℤ) r) r)
       (Cos (10:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_10

theorem cos_11 : ∀ r ≤ 23, Holds (Cos (11:ℤ) r) (b r (Real.pi*((11:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (11:ℤ)) (Z := cosZI (11:ℤ)) (S := point 0) (C := signI (11:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (11:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (11:ℤ)) (point 0) (signI (11:ℤ)) (Cos (11:ℤ) r) r)
       (Cos (11:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_11

theorem cos_12 : ∀ r ≤ 23, Holds (Cos (12:ℤ) r) (b r (Real.pi*((12:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (12:ℤ)) (Z := cosZI (12:ℤ)) (S := point 0) (C := signI (12:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (12:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (12:ℤ)) (point 0) (signI (12:ℤ)) (Cos (12:ℤ) r) r)
       (Cos (12:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_12

theorem cos_13 : ∀ r ≤ 23, Holds (Cos (13:ℤ) r) (b r (Real.pi*((13:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (13:ℤ)) (Z := cosZI (13:ℤ)) (S := point 0) (C := signI (13:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (13:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (13:ℤ)) (point 0) (signI (13:ℤ)) (Cos (13:ℤ) r) r)
       (Cos (13:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_13

theorem cos_14 : ∀ r ≤ 23, Holds (Cos (14:ℤ) r) (b r (Real.pi*((14:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (14:ℤ)) (Z := cosZI (14:ℤ)) (S := point 0) (C := signI (14:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (14:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (14:ℤ)) (point 0) (signI (14:ℤ)) (Cos (14:ℤ) r) r)
       (Cos (14:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_14

theorem cos_15 : ∀ r ≤ 23, Holds (Cos (15:ℤ) r) (b r (Real.pi*((15:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (15:ℤ)) (Z := cosZI (15:ℤ)) (S := point 0) (C := signI (15:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (15:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (15:ℤ)) (point 0) (signI (15:ℤ)) (Cos (15:ℤ) r) r)
       (Cos (15:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_15

end StructuralGoal20261016.WindowJetTableBounds
end
