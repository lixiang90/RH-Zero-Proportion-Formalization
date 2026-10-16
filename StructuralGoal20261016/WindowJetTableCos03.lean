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
theorem cos_0 : ∀ r ≤ 23, Holds (Cos (0:ℤ) r) (b r (Real.pi*((0:ℤ):ℝ))) := by
 simpa only [Int.cast_zero,mul_zero] using pole_table_sound E (Cos 0) e_sound
   (by
     have h : ∀ r : Fin 24, covers
       (rmul (E r) (phaseI (point 0) (point 1) r).2) (Cos 0 r) = true := by decide +kernel
     intro r hr
     exact h ⟨r,by omega⟩)
#print axioms cos_0

theorem cos_1 : ∀ r ≤ 23, Holds (Cos (1:ℤ) r) (b r (Real.pi*((1:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (1:ℤ)) (Z := cosZI (1:ℤ)) (S := point 0) (C := signI (1:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (1:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (1:ℤ)) (point 0) (signI (1:ℤ)) (Cos (1:ℤ) r) r)
       (Cos (1:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_1

theorem cos_2 : ∀ r ≤ 23, Holds (Cos (2:ℤ) r) (b r (Real.pi*((2:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (2:ℤ)) (Z := cosZI (2:ℤ)) (S := point 0) (C := signI (2:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (2:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (2:ℤ)) (point 0) (signI (2:ℤ)) (Cos (2:ℤ) r) r)
       (Cos (2:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_2

theorem cos_3 : ∀ r ≤ 23, Holds (Cos (3:ℤ) r) (b r (Real.pi*((3:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (3:ℤ)) (Z := cosZI (3:ℤ)) (S := point 0) (C := signI (3:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (3:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (3:ℤ)) (point 0) (signI (3:ℤ)) (Cos (3:ℤ) r) r)
       (Cos (3:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_3

theorem cos_4 : ∀ r ≤ 23, Holds (Cos (4:ℤ) r) (b r (Real.pi*((4:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (4:ℤ)) (Z := cosZI (4:ℤ)) (S := point 0) (C := signI (4:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (4:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (4:ℤ)) (point 0) (signI (4:ℤ)) (Cos (4:ℤ) r) r)
       (Cos (4:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_4

theorem cos_5 : ∀ r ≤ 23, Holds (Cos (5:ℤ) r) (b r (Real.pi*((5:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (5:ℤ)) (Z := cosZI (5:ℤ)) (S := point 0) (C := signI (5:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (5:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (5:ℤ)) (point 0) (signI (5:ℤ)) (Cos (5:ℤ) r) r)
       (Cos (5:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_5

theorem cos_6 : ∀ r ≤ 23, Holds (Cos (6:ℤ) r) (b r (Real.pi*((6:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (6:ℤ)) (Z := cosZI (6:ℤ)) (S := point 0) (C := signI (6:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (6:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (6:ℤ)) (point 0) (signI (6:ℤ)) (Cos (6:ℤ) r) r)
       (Cos (6:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_6

theorem cos_7 : ∀ r ≤ 23, Holds (Cos (7:ℤ) r) (b r (Real.pi*((7:ℤ):ℝ))) := by
 apply b_table_sound E (Cos (7:ℤ)) (Z := cosZI (7:ℤ)) (S := point 0) (C := signI (7:ℤ)) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound (7:ℤ)
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI (7:ℤ)) (point 0) (signI (7:ℤ)) (Cos (7:ℤ) r) r)
       (Cos (7:ℤ) ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms cos_7

end StructuralGoal20261016.WindowJetTableBounds
end
