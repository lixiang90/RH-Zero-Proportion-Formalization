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
theorem cos_32 : ∀ r ≤ 23, Holds (Cos (32:ℤ) r) (b r (Real.pi*((32:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (32:ℤ)) (Z := cosZI (32:ℤ)) (S := point 0) (C := signI (32:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (32:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (32:ℤ)) (point 0) (signI (32:ℤ)) (Cos (32:ℤ) r) r)
       (Cos (32:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_32

theorem cos_33 : ∀ r ≤ 23, Holds (Cos (33:ℤ) r) (b r (Real.pi*((33:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (33:ℤ)) (Z := cosZI (33:ℤ)) (S := point 0) (C := signI (33:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (33:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (33:ℤ)) (point 0) (signI (33:ℤ)) (Cos (33:ℤ) r) r)
       (Cos (33:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_33

theorem cos_34 : ∀ r ≤ 23, Holds (Cos (34:ℤ) r) (b r (Real.pi*((34:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (34:ℤ)) (Z := cosZI (34:ℤ)) (S := point 0) (C := signI (34:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (34:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (34:ℤ)) (point 0) (signI (34:ℤ)) (Cos (34:ℤ) r) r)
       (Cos (34:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_34

theorem cos_35 : ∀ r ≤ 23, Holds (Cos (35:ℤ) r) (b r (Real.pi*((35:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (35:ℤ)) (Z := cosZI (35:ℤ)) (S := point 0) (C := signI (35:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (35:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (35:ℤ)) (point 0) (signI (35:ℤ)) (Cos (35:ℤ) r) r)
       (Cos (35:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_35

theorem cos_36 : ∀ r ≤ 23, Holds (Cos (36:ℤ) r) (b r (Real.pi*((36:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (36:ℤ)) (Z := cosZI (36:ℤ)) (S := point 0) (C := signI (36:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (36:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (36:ℤ)) (point 0) (signI (36:ℤ)) (Cos (36:ℤ) r) r)
       (Cos (36:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_36

theorem cos_37 : ∀ r ≤ 23, Holds (Cos (37:ℤ) r) (b r (Real.pi*((37:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (37:ℤ)) (Z := cosZI (37:ℤ)) (S := point 0) (C := signI (37:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (37:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (37:ℤ)) (point 0) (signI (37:ℤ)) (Cos (37:ℤ) r) r)
       (Cos (37:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_37

theorem cos_38 : ∀ r ≤ 23, Holds (Cos (38:ℤ) r) (b r (Real.pi*((38:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (38:ℤ)) (Z := cosZI (38:ℤ)) (S := point 0) (C := signI (38:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (38:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (38:ℤ)) (point 0) (signI (38:ℤ)) (Cos (38:ℤ) r) r)
       (Cos (38:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_38

theorem cos_39 : ∀ r ≤ 23, Holds (Cos (39:ℤ) r) (b r (Real.pi*((39:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (39:ℤ)) (Z := cosZI (39:ℤ)) (S := point 0) (C := signI (39:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (39:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (39:ℤ)) (point 0) (signI (39:ℤ)) (Cos (39:ℤ) r) r)
       (Cos (39:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_39

end StructuralGoal20261016.WindowJetTableBounds
end
