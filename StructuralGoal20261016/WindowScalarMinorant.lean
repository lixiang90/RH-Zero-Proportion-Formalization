/- SPDX-License-Identifier: Apache-2.0
Actual scalar quadratic minorants from convexity and finite point jets.
The generic analytic implication is separated from the rational table checks.
-/
import StructuralGoal20261016.WindowConvexityCertificate
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set
open scoped BigOperators
namespace StructuralGoal20261016.WindowScalarMinorant
open WindowKernel WindowTaylorBridge WindowConvexityCertificate

abbrev f : ℝ → ℝ := w 24 d24

theorem taylor_one (p x : ℝ) :
 taylorPoly f 1 p x = f p+iteratedDeriv 1 f p*(x-p) := by
 simp only [taylorPoly, Finset.sum_range_succ, Finset.sum_range_zero,
   zero_add, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one,
   pow_zero, pow_one, mul_one, iteratedDeriv_zero]

theorem quadratic_tangent {a b A p x : ℝ} (hp : p ∈ Icc a b) (hx : x ∈ Icc a b)
 (hsecond : ∀ y ∈ Icc a b, 2*A ≤ iteratedDeriv 2 f y) :
 f p+iteratedDeriv 1 f p*(x-p)+A*(x-p)^2 ≤ f x := by
 by_cases hpx : p = x
 · subst x
   simp
 · have hu : UniqueDiffOn ℝ (uIcc p x) := uniqueDiffOn_Icc (by grind)
   obtain ⟨y, hy, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
     (n := 1) hpx (w_contDiff 24 d24 2).contDiffOn
   rw [taylorWithin_eq_poly f (fun n => w_contDiff 24 d24 n) 1
     (uIcc p x) hu left_mem_uIcc, taylor_one] at he
   have hy' : y ∈ Icc a b := by
     have hh := uIoo_subset_uIcc_self hy
     rw [mem_uIcc] at hh
     rcases hh with hh | hh <;> constructor <;> linarith [hp.1, hp.2, hx.1, hx.2]
   have hs := mul_le_mul_of_nonneg_right (hsecond y hy') (sq_nonneg (x-p))
   norm_num at he
   change f x-(f p+deriv f p*(x-p)) = iteratedDeriv 2 f y*(x-p)^2/2 at he
   simp only [iteratedDeriv_one]
   nlinarith only [he, hs]

theorem quadratic_minorant {a b A p x V S ε radius : ℝ}
 (hp : p ∈ Icc a b) (hx : x ∈ Icc a b) (hε : 0 ≤ ε)
 (hr : |x-p| ≤ radius)
 (hsecond : ∀ y ∈ Icc a b, 2*A ≤ iteratedDeriv 2 f y)
 (hV : V+ε*radius ≤ f p) (hS : |iteratedDeriv 1 f p-S| ≤ ε) :
 V+S*(x-p)+A*(x-p)^2 ≤ f x := by
 have ht := quadratic_tangent hp hx hsecond
 have he : |(iteratedDeriv 1 f p-S)*(x-p)| ≤ ε*radius := by
   rw [abs_mul]
   exact mul_le_mul hS hr (abs_nonneg _) hε
 have hl := (abs_le.mp he).1
 nlinarith only [ht, hV, hl]

theorem value_remainder (p x : ℝ) :
 |f x-taylorPoly f 23 p x| ≤
   (44/7 : ℝ)^24*|x-p|^24/((24:ℕ).factorial:ℝ) := by
 exact taylor_remainder f (fun n => w_contDiff 24 d24 n) 23
   (w24_twentyfour_abs_le) p x

theorem slope_remainder (p x : ℝ) :
 |iteratedDeriv 1 f x-taylorPoly (iteratedDeriv 1 f) 22 p x| ≤
   (44/7 : ℝ)^24*|x-p|^23/((23:ℕ).factorial:ℝ) := by
 apply taylor_remainder (iteratedDeriv 1 f)
   (fun n => w_iterated_contDiff 24 d24 1 n) 22
 intro y
 rw [iterated_iterated]
 exact w24_twentyfour_abs_le y

theorem value_lower_from_taylor {p x V R : ℝ}
 (hR : (44/7 : ℝ)^24*|x-p|^24/((24:ℕ).factorial:ℝ) ≤ R)
 (hpoly : V+R ≤ taylorPoly f 23 p x) : V ≤ f x := by
 have h := (value_remainder p x).trans hR
 linarith [(abs_le.mp h).1]

theorem slope_interval_from_taylor {p x L U R : ℝ}
 (hR : (44/7 : ℝ)^24*|x-p|^23/((23:ℕ).factorial:ℝ) ≤ R)
 (hl : L+R ≤ taylorPoly (iteratedDeriv 1 f) 22 p x)
 (hu : taylorPoly (iteratedDeriv 1 f) 22 p x ≤ U-R) :
 L ≤ iteratedDeriv 1 f x ∧ iteratedDeriv 1 f x ≤ U := by
 have h := (slope_remainder p x).trans hR
 exact ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩

#print axioms quadratic_minorant
#print axioms value_lower_from_taylor
#print axioms slope_interval_from_taylor
end StructuralGoal20261016.WindowScalarMinorant
end
