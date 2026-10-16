/- SPDX-License-Identifier: Apache-2.0
One-sided Taylor upper bounds for actual finite-move difference kernels.
An upper bound on the signed second derivative is enough: strictly concave
old wells need no artificial absolute-curvature radius penalty.
-/
import StructuralGoal20261016.WindowScalarMinorant
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowFiniteMoveScalar
open WindowKernel WindowTaylorBridge WindowConvexityCertificate

def h (s x : ℝ) : ℝ := w 24 d24 (x+s)-w 24 d24 x

theorem h_contDiff (s : ℝ) (n : ℕ) : ContDiff ℝ n (h s) := by
  exact ((w_contDiff 24 d24 n).comp (contDiff_id.add contDiff_const)).sub (w_contDiff 24 d24 n)

theorem w_iterated_hasDerivAt (r : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv r (w 24 d24)) (iteratedDeriv (r+1) (w 24 d24) x) x := by
  simpa only [iteratedDeriv_succ] using
    (((w_iterated_contDiff 24 d24 r 1).differentiable (by norm_num)) x).hasDerivAt

/-- Shared-coordinate differences retain cancellation before interval
evaluation. This identity lets both integer-centred actual tables be used
for a single difference polynomial, instead of two unrelated ranges. -/
theorem iterated_h (s : ℝ) (r : ℕ) :
    iteratedDeriv r (h s) = fun x =>
      iteratedDeriv r (w 24 d24) (x+s)-iteratedDeriv r (w 24 d24) x := by
  induction r with
  | zero =>
    simp only [iteratedDeriv_zero]
    rfl
  | succ r ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    have hi : HasDerivAt (fun y : ℝ => y+s) 1 x := (hasDerivAt_id x).add_const s
    have hp := (w_iterated_hasDerivAt r (x+s)).comp x hi
    have hd := hp.sub (w_iterated_hasDerivAt r x)
    change HasDerivAt (fun y : ℝ =>
      iteratedDeriv r (w 24 d24) (y+s)-iteratedDeriv r (w 24 d24) y)
      (iteratedDeriv (r+1) (w 24 d24) (x+s)*1-iteratedDeriv (r+1) (w 24 d24) x) x at hd
    simpa only [mul_one] using hd.deriv

theorem taylor_one (s p x : ℝ) :
    taylorPoly (h s) 1 p x = h s p+iteratedDeriv 1 (h s) p*(x-p) := by
  simp only [taylorPoly,Finset.sum_range_succ,Finset.sum_range_zero,
    zero_add,Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,div_one,
    pow_zero,pow_one,mul_one,iteratedDeriv_zero]

theorem quadratic_upper {s a b A p x : ℝ}
    (hp : p ∈ Icc a b) (hx : x ∈ Icc a b)
    (hsecond : ∀ y ∈ Icc a b, iteratedDeriv 2 (h s) y ≤ 2*A) :
    h s x ≤ h s p+iteratedDeriv 1 (h s) p*(x-p)+A*(x-p)^2 := by
  by_cases hpx : p = x
  · subst x
    simp
  · have hu : UniqueDiffOn ℝ (uIcc p x) := uniqueDiffOn_Icc (by grind)
    obtain ⟨y,hy,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
      (n := 1) hpx (h_contDiff s 2).contDiffOn
    rw [taylorWithin_eq_poly (h s) (h_contDiff s) 1
      (uIcc p x) hu left_mem_uIcc,taylor_one] at he
    have hy' : y ∈ Icc a b := by
      have hh := uIoo_subset_uIcc_self hy
      rw [mem_uIcc] at hh
      rcases hh with hh | hh <;> constructor <;> linarith [hp.1,hp.2,hx.1,hx.2]
    have hs := mul_le_mul_of_nonneg_right (hsecond y hy') (sq_nonneg (x-p))
    norm_num at he
    change h s x-(h s p+deriv (h s) p*(x-p)) = iteratedDeriv 2 (h s) y*(x-p)^2/2 at he
    simp only [iteratedDeriv_one]
    nlinarith only [he,hs]

theorem affine_upper {s a b A p x V D E radius : ℝ}
    (hp : p ∈ Icc a b) (hx : x ∈ Icc a b)
    (hsecond : ∀ y ∈ Icc a b, iteratedDeriv 2 (h s) y ≤ 2*A)
    (hV : h s p ≤ V) (hE : 0 ≤ E)
    (hD : |iteratedDeriv 1 (h s) p-D| ≤ E) (hr : |x-p| ≤ radius) :
    h s x ≤ V+D*(x-p)+E*radius+max A 0*radius^2 := by
  have ht := quadratic_upper hp hx hsecond
  have he : |(iteratedDeriv 1 (h s) p-D)*(x-p)| ≤ E*radius := by
    rw [abs_mul]
    exact mul_le_mul hD hr (abs_nonneg _) hE
  have hsq : (x-p)^2 ≤ radius^2 := by
    have habs := abs_nonneg (x-p)
    rcases abs_le.mp hr with ⟨hl,hu⟩
    nlinarith
  have hcurv : A*(x-p)^2 ≤ max A 0*radius^2 := by
    calc
      A*(x-p)^2 ≤ max A 0*(x-p)^2 :=
        mul_le_mul_of_nonneg_right (le_max_left A 0) (sq_nonneg (x-p))
      _ ≤ max A 0*radius^2 :=
        mul_le_mul_of_nonneg_left hsq (le_max_right A 0)
  nlinarith only [ht,hV,(abs_le.mp he).2,hcurv]

theorem concave_affine_upper {s a b p x V D E radius : ℝ}
    (hp : p ∈ Icc a b) (hx : x ∈ Icc a b)
    (hsecond : ∀ y ∈ Icc a b, iteratedDeriv 2 (h s) y ≤ 0)
    (hV : h s p ≤ V) (hE : 0 ≤ E)
    (hD : |iteratedDeriv 1 (h s) p-D| ≤ E) (hr : |x-p| ≤ radius) :
    h s x ≤ V+D*(x-p)+E*radius := by
  have ht := affine_upper (A := 0) hp hx (by simpa using hsecond) hV hE hD hr
  simpa using ht

set_option pp.fullNames true
#print axioms h_contDiff
#print axioms iterated_h
#print axioms quadratic_upper
#print axioms affine_upper
#print axioms concave_affine_upper
end StructuralGoal20261016.WindowFiniteMoveScalar
end
