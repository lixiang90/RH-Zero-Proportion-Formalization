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
theorem cos_40 : ∀ r ≤ 23, Holds (Cos (40:ℤ) r) (b r (Real.pi*((40:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (40:ℤ)) (Z := cosZI (40:ℤ)) (S := point 0) (C := signI (40:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (40:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (40:ℤ)) (point 0) (signI (40:ℤ)) (Cos (40:ℤ) r) r)
       (Cos (40:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_40

theorem cos_41 : ∀ r ≤ 23, Holds (Cos (41:ℤ) r) (b r (Real.pi*((41:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (41:ℤ)) (Z := cosZI (41:ℤ)) (S := point 0) (C := signI (41:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (41:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (41:ℤ)) (point 0) (signI (41:ℤ)) (Cos (41:ℤ) r) r)
       (Cos (41:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_41

theorem cos_42 : ∀ r ≤ 23, Holds (Cos (42:ℤ) r) (b r (Real.pi*((42:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (42:ℤ)) (Z := cosZI (42:ℤ)) (S := point 0) (C := signI (42:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (42:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (42:ℤ)) (point 0) (signI (42:ℤ)) (Cos (42:ℤ) r) r)
       (Cos (42:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_42

theorem cos_43 : ∀ r ≤ 23, Holds (Cos (43:ℤ) r) (b r (Real.pi*((43:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (43:ℤ)) (Z := cosZI (43:ℤ)) (S := point 0) (C := signI (43:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (43:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (43:ℤ)) (point 0) (signI (43:ℤ)) (Cos (43:ℤ) r) r)
       (Cos (43:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_43

theorem cos_44 : ∀ r ≤ 23, Holds (Cos (44:ℤ) r) (b r (Real.pi*((44:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (44:ℤ)) (Z := cosZI (44:ℤ)) (S := point 0) (C := signI (44:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (44:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (44:ℤ)) (point 0) (signI (44:ℤ)) (Cos (44:ℤ) r) r)
       (Cos (44:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_44

theorem cos_45 : ∀ r ≤ 23, Holds (Cos (45:ℤ) r) (b r (Real.pi*((45:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (45:ℤ)) (Z := cosZI (45:ℤ)) (S := point 0) (C := signI (45:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (45:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (45:ℤ)) (point 0) (signI (45:ℤ)) (Cos (45:ℤ) r) r)
       (Cos (45:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_45

theorem cos_46 : ∀ r ≤ 23, Holds (Cos (46:ℤ) r) (b r (Real.pi*((46:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (46:ℤ)) (Z := cosZI (46:ℤ)) (S := point 0) (C := signI (46:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (46:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (46:ℤ)) (point 0) (signI (46:ℤ)) (Cos (46:ℤ) r) r)
       (Cos (46:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_46

theorem cos_47 : ∀ r ≤ 23, Holds (Cos (47:ℤ) r) (b r (Real.pi*((47:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (47:ℤ)) (Z := cosZI (47:ℤ)) (S := point 0) (C := signI (47:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (47:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (47:ℤ)) (point 0) (signI (47:ℤ)) (Cos (47:ℤ) r) r)
       (Cos (47:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_47

end StructuralGoal20261016.WindowJetTableBounds
end
