/- SPDX-License-Identifier: Apache-2.0
Fraction-free finite Bernstein checks for actual second-derivative bounds.
Every coefficient sum is linear in stored integer endpoints. The exact
power-to-Bernstein identity and Fourier Taylor remainder are already proved.
-/
import StructuralGoal20261016.WindowFixedPolynomial
import StructuralGoal20261016.WindowFixedKernel
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set
open scoped BigOperators
namespace StructuralGoal20261016.WindowFixedConvexity
open WindowRationalInterval (Holds)
open WindowFixedInterval WindowFixedRational WindowFixedPolynomial
open WindowConvexityCertificate WindowBernsteinTransform WindowNormalizedJets WindowJetTableData

def power (C : ℕ → FI) (l h : ℚ) (j : ℕ) : FI :=
 WindowFixedKernel.FI.sum (fun i => if j ≤ i then
   scale (C i) ((i.choose j:ℚ)*l^(i-j)*h^j) else point 0) 14
def bernstein (C : ℕ → FI) (l h : ℚ) (k : ℕ) : FI :=
 WindowFixedKernel.FI.sum (fun j => scale (power C l h j)
   ((k.choose j:ℚ)/((13:ℕ).choose j:ℚ))) 14

theorem power_sound (C : ℕ → FI) (a : ℕ → ℝ) (l h : ℚ)
 (hC : ∀ i < 14, Holds (decode (C i)) (a i)) (j : ℕ) :
 Holds (decode (power C l h j)) (powerCoeff a l h j) := by
 unfold powerCoeff
 apply WindowFixedKernel.FI.sum_sound
 intro i hi
 split_ifs with hji
 · have hh := scale_sound (hC i hi) ((i.choose j:ℚ)*l^(i-j)*h^j)
   convert hh using 1 <;> push_cast <;> ring
 · simpa only [Int.cast_zero] using point_sound 0

theorem bernstein_sound (C : ℕ → FI) (a : ℕ → ℝ) (l h : ℚ)
 (hC : ∀ i < 14, Holds (decode (C i)) (a i)) (k : ℕ) :
 Holds (decode (bernstein C l h k)) (beta a l h k) := by
 unfold beta
 apply WindowFixedKernel.FI.sum_sound
 intro j hj
 have hh := scale_sound (power_sound C a l h hC j) ((k.choose j:ℚ)/((13:ℕ).choose j:ℚ))
 convert hh using 1 <;> push_cast <;> ring

def secondCoeff (n j : ℕ) : FI := scale (ofQI (W n (j+2))) ((j+1)*(j+2))

theorem secondCoeff_sound {n : ℕ}
 (hW : ∀ j ≤ 23, Holds (W n j) (wc 24 WindowKernel.d24 j (n:ℝ))) :
 ∀ j < 14, Holds (decode (secondCoeff n j)) (iteratedDeriv j wSecond (n:ℝ)/(j.factorial:ℝ)) := by
 intro j hj
 rw [WindowConvexityArithmetic.second_coeff]
 have hh := scale_sound (ofQI_sound (hW (j+2) (by omega))) ((j+1)*(j+2))
 unfold secondCoeff
 convert hh using 1 <;> push_cast <;> ring

theorem actual_convex_piece (C : ℕ → FI) (a b p radius R L : ℚ)
 (hab : a < b) (hr : 0 ≤ radius)
 (hC : ∀ j < 14, Holds (decode (C j)) (iteratedDeriv j wSecond p/(j.factorial:ℝ)))
 (hrad : ∀ x ∈ Icc (a:ℝ) b, |x-p| ≤ radius)
 (hR : (44/7:ℚ)^16*radius^14/(14:ℕ).factorial ≤ R)
 (hβ : ∀ k < 14, lowerCheck (bernstein C (a-p) (b-a) k) (L+R) = true) :
 ∀ x ∈ Icc (a:ℝ) b, (L:ℝ) ≤ wSecond x := by
 apply wSecond_lower_from_Bernstein
   (a := (a:ℝ)) (b := (b:ℝ)) (p := (p:ℝ)) (radius := (radius:ℝ))
   (R := (R:ℝ)) (L := (L:ℝ))
   (β := beta (fun j => iteratedDeriv j wSecond p/(j.factorial:ℝ)) ((a:ℝ)-p) ((b:ℝ)-a))
 · exact_mod_cast hab
 · exact_mod_cast hr
 · exact hrad
 · have hh : (((44/7:ℚ)^16*radius^14/(14:ℕ).factorial:ℚ):ℝ) ≤ (R:ℝ) :=
     Rat.cast_le.mpr hR
   push_cast at hh
   exact hh
 · intro u
   exact taylor_identity13 wSecond p a b u
 · intro k hk
   have hb := lowerCheck_sound (hβ k (Finset.mem_range.mp hk))
     (bernstein_sound C (fun j => iteratedDeriv j wSecond p/(j.factorial:ℝ)) (a-p) (b-a) hC k)
   push_cast at hb
   exact hb

set_option pp.fullNames true
#print axioms bernstein_sound
#print axioms secondCoeff_sound
#print axioms actual_convex_piece
end StructuralGoal20261016.WindowFixedConvexity
end
