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
theorem cos_48 : ∀ r ≤ 23, Holds (Cos (48:ℤ) r) (b r (Real.pi*((48:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (48:ℤ)) (Z := cosZI (48:ℤ)) (S := point 0) (C := signI (48:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (48:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (48:ℤ)) (point 0) (signI (48:ℤ)) (Cos (48:ℤ) r) r)
       (Cos (48:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_48

theorem cos_49 : ∀ r ≤ 23, Holds (Cos (49:ℤ) r) (b r (Real.pi*((49:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (49:ℤ)) (Z := cosZI (49:ℤ)) (S := point 0) (C := signI (49:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (49:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (49:ℤ)) (point 0) (signI (49:ℤ)) (Cos (49:ℤ) r) r)
       (Cos (49:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_49

theorem cos_50 : ∀ r ≤ 23, Holds (Cos (50:ℤ) r) (b r (Real.pi*((50:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (50:ℤ)) (Z := cosZI (50:ℤ)) (S := point 0) (C := signI (50:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (50:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (50:ℤ)) (point 0) (signI (50:ℤ)) (Cos (50:ℤ) r) r)
       (Cos (50:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_50

theorem cos_51 : ∀ r ≤ 23, Holds (Cos (51:ℤ) r) (b r (Real.pi*((51:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (51:ℤ)) (Z := cosZI (51:ℤ)) (S := point 0) (C := signI (51:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (51:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (51:ℤ)) (point 0) (signI (51:ℤ)) (Cos (51:ℤ) r) r)
       (Cos (51:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_51

theorem cos_52 : ∀ r ≤ 23, Holds (Cos (52:ℤ) r) (b r (Real.pi*((52:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (52:ℤ)) (Z := cosZI (52:ℤ)) (S := point 0) (C := signI (52:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (52:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (52:ℤ)) (point 0) (signI (52:ℤ)) (Cos (52:ℤ) r) r)
       (Cos (52:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_52

theorem cos_53 : ∀ r ≤ 23, Holds (Cos (53:ℤ) r) (b r (Real.pi*((53:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (53:ℤ)) (Z := cosZI (53:ℤ)) (S := point 0) (C := signI (53:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (53:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (53:ℤ)) (point 0) (signI (53:ℤ)) (Cos (53:ℤ) r) r)
       (Cos (53:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_53

theorem cos_54 : ∀ r ≤ 23, Holds (Cos (54:ℤ) r) (b r (Real.pi*((54:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (54:ℤ)) (Z := cosZI (54:ℤ)) (S := point 0) (C := signI (54:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (54:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (54:ℤ)) (point 0) (signI (54:ℤ)) (Cos (54:ℤ) r) r)
       (Cos (54:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_54

theorem cos_55 : ∀ r ≤ 23, Holds (Cos (55:ℤ) r) (b r (Real.pi*((55:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (55:ℤ)) (Z := cosZI (55:ℤ)) (S := point 0) (C := signI (55:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (55:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (55:ℤ)) (point 0) (signI (55:ℤ)) (Cos (55:ℤ) r) r)
       (Cos (55:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_55

end StructuralGoal20261016.WindowJetTableBounds
end
