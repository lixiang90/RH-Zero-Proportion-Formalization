/- SPDX-License-Identifier: Apache-2.0
Sound interval arithmetic for the actual degree-13 Bernstein convexity
certificates, expressed in factorial-normalized w coefficients.
-/
import StructuralGoal20261016.WindowBernsteinTransform
import StructuralGoal20261016.WindowJetTableConsumer
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real
open scoped BigOperators
namespace StructuralGoal20261016.WindowConvexityArithmetic
open WindowRationalInterval WindowNormalizedJets WindowIntegerKernelRecipe
open WindowConvexityCertificate WindowBernsteinTransform

theorem first_coeff (j : ℕ) (p : ℝ) :
 iteratedDeriv j (iteratedDeriv 1 (WindowKernel.w 24 WindowKernel.d24)) p/(j.factorial:ℝ) =
   (j+1:ℕ)*wc 24 WindowKernel.d24 (j+1) p := by
 rw [iterated_iterated]
 unfold wc
 rw [Nat.factorial_succ]
 have hj : (j.factorial:ℝ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
 have hj1 : ((j+1:ℕ):ℝ) ≠ 0 := by positivity
 push_cast
 field_simp [hj,hj1]
 <;> ring

theorem second_coeff (j : ℕ) (p : ℝ) :
 iteratedDeriv j wSecond p/(j.factorial:ℝ) =
   ((j+1:ℕ):ℝ)*(j+2:ℕ)*wc 24 WindowKernel.d24 (j+2) p := by
 unfold wSecond
 rw [iterated_iterated]
 unfold wc
 rw [show j+2 = (j+1)+1 by omega, Nat.factorial_succ, Nat.factorial_succ]
 have hj : (j.factorial:ℝ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
 have hj1 : ((j+1:ℕ):ℝ) ≠ 0 := by positivity
 have hj2 : ((j+2:ℕ):ℝ) ≠ 0 := by positivity
 push_cast
 field_simp [hj,hj1,hj2]
 <;> ring

def powerCoeffI (C : ℕ → QI) (l h : ℚ) (j : ℕ) : QI :=
 sumI (fun i => if j ≤ i then
   rmul (rmul (rmul (C i) (point (i.choose j))) (pow (point l) (i-j)))
     (pow (point h) j) else point 0) 14

theorem powerCoeffI_sound (C : ℕ → QI) (a : ℕ → ℝ) (l h : ℚ)
 (hC : ∀ i < 14, Holds (C i) (a i)) (j : ℕ) :
 Holds (powerCoeffI C l h j) (powerCoeff a l h j) := by
 unfold powerCoeff
 apply sumI_sound
 intro i hi
 split_ifs with hji
 · apply rmul_sound
   · apply rmul_sound
     · exact rmul_sound (hC i hi)
         (by simpa only [Rat.cast_natCast] using point_sound (i.choose j:ℚ))
     · exact pow_sound (point_sound l) (i-j)
   · exact pow_sound (point_sound h) j
 · norm_num [Holds,point]

def betaI (C : ℕ → QI) (l h : ℚ) (k : ℕ) : QI :=
 sumI (fun j => rdiv (rmul (powerCoeffI C l h j) (point (k.choose j)))
   (point ((13:ℕ).choose j))) 14

theorem betaI_sound (C : ℕ → QI) (a : ℕ → ℝ) (l h : ℚ)
 (hC : ∀ i < 14, Holds (C i) (a i)) (k : ℕ) :
 Holds (betaI C l h k) (beta a l h k) := by
 unfold beta
 apply sumI_sound
 intro j hj
 apply rdiv_sound
 · exact rmul_sound (powerCoeffI_sound C a l h hC j)
     (by simpa only [Rat.cast_natCast] using point_sound (k.choose j:ℚ))
 · simpa only [Rat.cast_natCast] using point_sound ((13:ℕ).choose j:ℚ)
 · left
   dsimp [point]
   exact_mod_cast Nat.choose_pos (by omega : j ≤ 13)

theorem actual_convex_piece (C : ℕ → QI) (a b p radius R L : ℚ)
 (hab : a < b) (hr : 0 ≤ radius)
 (hC : ∀ j < 14, Holds (C j) (iteratedDeriv j wSecond p/(j.factorial:ℝ)))
 (hrad : ∀ x ∈ Set.Icc (a:ℝ) b, |x-p| ≤ radius)
 (hR : (44/7 : ℚ)^16*radius^14/(14:ℕ).factorial ≤ R)
 (hβ : ∀ k < 14, L+R ≤ (betaI C (a-p) (b-a) k).1) :
 ∀ x ∈ Set.Icc (a:ℝ) b, (L:ℝ) ≤ wSecond x := by
 apply wSecond_lower_from_Bernstein
   (a := (a:ℝ)) (b := (b:ℝ)) (p := (p:ℝ)) (radius := (radius:ℝ))
   (R := (R:ℝ)) (L := (L:ℝ))
   (β := beta (fun j => iteratedDeriv j wSecond p/(j.factorial:ℝ)) ((a:ℝ)-p) ((b:ℝ)-a))
 · exact_mod_cast hab
 · exact_mod_cast hr
 · exact hrad
 · have hh : (((44/7 : ℚ)^16*radius^14/(14:ℕ).factorial:ℚ):ℝ) ≤ (R:ℝ) := by
     exact Rat.cast_le.mpr hR
   push_cast at hh
   exact hh
 · intro u
   exact taylor_identity13 wSecond p a b u
 · intro k hk
   have hb := (betaI_sound C
     (fun j => iteratedDeriv j wSecond p/(j.factorial:ℝ)) (a-p) (b-a) hC k).1
   have hl : ((L+R:ℚ):ℝ) ≤ ((betaI C (a-p) (b-a) k).1:ℝ) := by
     exact_mod_cast hβ k (Finset.mem_range.mp hk)
   push_cast at hb hl
   exact hl.trans hb

set_option pp.fullNames true
#print axioms betaI_sound
#print axioms actual_convex_piece
end StructuralGoal20261016.WindowConvexityArithmetic
end
