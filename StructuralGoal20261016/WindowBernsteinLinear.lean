/- SPDX-License-Identifier: Apache-2.0
Exact linearization of each degree-13 Bernstein coefficient in the original
Taylor coefficients. The rational weights depend only on the subinterval,
so they can be checked once and reused for all sixteen integer wells.
-/
import StructuralGoal20261016.WindowFixedConvexity
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set
open scoped BigOperators
namespace StructuralGoal20261016.WindowBernsteinLinear
open WindowRationalInterval (Holds)
open WindowFixedInterval WindowFixedPolynomial
open WindowBernsteinTransform WindowConvexityCertificate

def weight (l h : ℝ) (k i : ℕ) : ℝ :=
 ∑ j ∈ Finset.range 14, if j ≤ i then
   (i.choose j:ℝ)*l^(i-j)*h^j*(k.choose j:ℝ)/((13:ℕ).choose j:ℝ) else 0
def weightQ (l h : ℚ) (k i : ℕ) : ℚ :=
 ∑ j ∈ Finset.range 14, if j ≤ i then
   (i.choose j:ℚ)*l^(i-j)*h^j*(k.choose j:ℚ)/((13:ℕ).choose j:ℚ) else 0

theorem cast_weightQ (l h : ℚ) (k i : ℕ) : (weightQ l h k i:ℝ) = weight l h k i := by
 unfold weightQ weight
 rw [Rat.cast_sum]
 apply Finset.sum_congr rfl
 intro j _
 split_ifs <;> push_cast <;> rfl

theorem beta_linear (a : ℕ → ℝ) (l h : ℝ) (k : ℕ) :
 beta a l h k = ∑ i ∈ Finset.range 14, a i*weight l h k i := by
 unfold beta powerCoeff weight
 simp_rw [Finset.sum_mul,Finset.sum_div,Finset.mul_sum]
 rw [Finset.sum_comm]
 apply Finset.sum_congr rfl
 intro i _
 apply Finset.sum_congr rfl
 intro j _
 split_ifs <;> ring

def weighted (C : ℕ → FI) (v : ℕ → ℚ) : FI :=
 WindowFixedKernel.FI.sum (fun i => scale (C i) (v i)) 14

theorem weighted_sound (C : ℕ → FI) (a : ℕ → ℝ) (v : ℕ → ℚ)
 (hC : ∀ i < 14, Holds (decode (C i)) (a i)) :
 Holds (decode (weighted C v)) (∑ i ∈ Finset.range 14, a i*(v i:ℝ)) :=
 WindowFixedKernel.FI.sum_sound _ _ _ (fun i hi => scale_sound (hC i hi) (v i))

theorem actual_convex_piece (C : ℕ → FI) (a b p radius R L : ℚ) (v : ℕ → ℕ → ℚ)
 (hab : a < b) (hr : 0 ≤ radius)
 (hC : ∀ j < 14, Holds (decode (C j)) (iteratedDeriv j wSecond p/(j.factorial:ℝ)))
 (hrad : ∀ x ∈ Icc (a:ℝ) b, |x-p| ≤ radius)
 (hR : (44/7:ℚ)^16*radius^14/(14:ℕ).factorial ≤ R)
 (hv : ∀ k < 14, ∀ i < 14, v k i = weightQ (a-p) (b-a) k i)
 (hβ : ∀ k < 14, lowerCheck (weighted C (v k)) (L+R) = true) :
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
   have hkn : k < 14 := Finset.mem_range.mp hk
   have hb := lowerCheck_sound (hβ k hkn)
     (weighted_sound C (fun j => iteratedDeriv j wSecond p/(j.factorial:ℝ)) (v k) hC)
   have he : (∑ i ∈ Finset.range 14, (iteratedDeriv i wSecond p/(i.factorial:ℝ))*(v k i:ℝ)) =
       beta (fun j => iteratedDeriv j wSecond p/(j.factorial:ℝ)) ((a:ℝ)-p) ((b:ℝ)-a) k := by
     rw [beta_linear]
     apply Finset.sum_congr rfl
     intro i hi
     rw [hv k hkn i (Finset.mem_range.mp hi),cast_weightQ]
     push_cast <;> rfl
   rw [he] at hb
   push_cast at hb
   exact hb

set_option pp.fullNames true
#print axioms beta_linear
#print axioms actual_convex_piece
end StructuralGoal20261016.WindowBernsteinLinear
end
