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
theorem cos_16 : ∀ r ≤ 23, Holds (Cos (16:ℤ) r) (b r (Real.pi*((16:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (16:ℤ)) (Z := cosZI (16:ℤ)) (S := point 0) (C := signI (16:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (16:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (16:ℤ)) (point 0) (signI (16:ℤ)) (Cos (16:ℤ) r) r)
       (Cos (16:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_16

theorem cos_17 : ∀ r ≤ 23, Holds (Cos (17:ℤ) r) (b r (Real.pi*((17:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (17:ℤ)) (Z := cosZI (17:ℤ)) (S := point 0) (C := signI (17:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (17:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (17:ℤ)) (point 0) (signI (17:ℤ)) (Cos (17:ℤ) r) r)
       (Cos (17:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_17

theorem cos_18 : ∀ r ≤ 23, Holds (Cos (18:ℤ) r) (b r (Real.pi*((18:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (18:ℤ)) (Z := cosZI (18:ℤ)) (S := point 0) (C := signI (18:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (18:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (18:ℤ)) (point 0) (signI (18:ℤ)) (Cos (18:ℤ) r) r)
       (Cos (18:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_18

theorem cos_19 : ∀ r ≤ 23, Holds (Cos (19:ℤ) r) (b r (Real.pi*((19:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (19:ℤ)) (Z := cosZI (19:ℤ)) (S := point 0) (C := signI (19:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (19:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (19:ℤ)) (point 0) (signI (19:ℤ)) (Cos (19:ℤ) r) r)
       (Cos (19:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_19

theorem cos_20 : ∀ r ≤ 23, Holds (Cos (20:ℤ) r) (b r (Real.pi*((20:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (20:ℤ)) (Z := cosZI (20:ℤ)) (S := point 0) (C := signI (20:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (20:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (20:ℤ)) (point 0) (signI (20:ℤ)) (Cos (20:ℤ) r) r)
       (Cos (20:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_20

theorem cos_21 : ∀ r ≤ 23, Holds (Cos (21:ℤ) r) (b r (Real.pi*((21:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (21:ℤ)) (Z := cosZI (21:ℤ)) (S := point 0) (C := signI (21:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (21:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (21:ℤ)) (point 0) (signI (21:ℤ)) (Cos (21:ℤ) r) r)
       (Cos (21:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_21

theorem cos_22 : ∀ r ≤ 23, Holds (Cos (22:ℤ) r) (b r (Real.pi*((22:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (22:ℤ)) (Z := cosZI (22:ℤ)) (S := point 0) (C := signI (22:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (22:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (22:ℤ)) (point 0) (signI (22:ℤ)) (Cos (22:ℤ) r) r)
       (Cos (22:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_22

theorem cos_23 : ∀ r ≤ 23, Holds (Cos (23:ℤ) r) (b r (Real.pi*((23:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (23:ℤ)) (Z := cosZI (23:ℤ)) (S := point 0) (C := signI (23:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (23:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (23:ℤ)) (point 0) (signI (23:ℤ)) (Cos (23:ℤ) r) r)
       (Cos (23:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_23

end StructuralGoal20261016.WindowJetTableBounds
end
