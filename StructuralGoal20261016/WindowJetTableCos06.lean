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
theorem cos_24 : ∀ r ≤ 23, Holds (Cos (24:ℤ) r) (b r (Real.pi*((24:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (24:ℤ)) (Z := cosZI (24:ℤ)) (S := point 0) (C := signI (24:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (24:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (24:ℤ)) (point 0) (signI (24:ℤ)) (Cos (24:ℤ) r) r)
       (Cos (24:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_24

theorem cos_25 : ∀ r ≤ 23, Holds (Cos (25:ℤ) r) (b r (Real.pi*((25:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (25:ℤ)) (Z := cosZI (25:ℤ)) (S := point 0) (C := signI (25:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (25:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (25:ℤ)) (point 0) (signI (25:ℤ)) (Cos (25:ℤ) r) r)
       (Cos (25:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_25

theorem cos_26 : ∀ r ≤ 23, Holds (Cos (26:ℤ) r) (b r (Real.pi*((26:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (26:ℤ)) (Z := cosZI (26:ℤ)) (S := point 0) (C := signI (26:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (26:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (26:ℤ)) (point 0) (signI (26:ℤ)) (Cos (26:ℤ) r) r)
       (Cos (26:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_26

theorem cos_27 : ∀ r ≤ 23, Holds (Cos (27:ℤ) r) (b r (Real.pi*((27:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (27:ℤ)) (Z := cosZI (27:ℤ)) (S := point 0) (C := signI (27:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (27:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (27:ℤ)) (point 0) (signI (27:ℤ)) (Cos (27:ℤ) r) r)
       (Cos (27:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_27

theorem cos_28 : ∀ r ≤ 23, Holds (Cos (28:ℤ) r) (b r (Real.pi*((28:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (28:ℤ)) (Z := cosZI (28:ℤ)) (S := point 0) (C := signI (28:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (28:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (28:ℤ)) (point 0) (signI (28:ℤ)) (Cos (28:ℤ) r) r)
       (Cos (28:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_28

theorem cos_29 : ∀ r ≤ 23, Holds (Cos (29:ℤ) r) (b r (Real.pi*((29:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (29:ℤ)) (Z := cosZI (29:ℤ)) (S := point 0) (C := signI (29:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (29:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (29:ℤ)) (point 0) (signI (29:ℤ)) (Cos (29:ℤ) r) r)
       (Cos (29:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_29

theorem cos_30 : ∀ r ≤ 23, Holds (Cos (30:ℤ) r) (b r (Real.pi*((30:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (30:ℤ)) (Z := cosZI (30:ℤ)) (S := point 0) (C := signI (30:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (30:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (30:ℤ)) (point 0) (signI (30:ℤ)) (Cos (30:ℤ) r) r)
       (Cos (30:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_30

theorem cos_31 : ∀ r ≤ 23, Holds (Cos (31:ℤ) r) (b r (Real.pi*((31:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (31:ℤ)) (Z := cosZI (31:ℤ)) (S := point 0) (C := signI (31:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (31:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (31:ℤ)) (point 0) (signI (31:ℤ)) (Cos (31:ℤ) r) r)
       (Cos (31:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_31

end StructuralGoal20261016.WindowJetTableBounds
end
