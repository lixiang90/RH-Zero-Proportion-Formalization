/- SPDX-License-Identifier: Apache-2.0
Taylor/Bernstein consumer for actual new-kernel convexity certificates.
The analytic remainder is discharged from the proved actual Fourier
derivative bounds. Only finite polynomial/jet coefficient obligations remain.
-/
import StructuralGoal20261016.WindowTaylorBridge
import Mathlib.Analysis.Calculus.Taylor
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory
open scoped BigOperators
namespace StructuralGoal20261016.WindowConvexityCertificate
open WindowKernel WindowTaylorBridge

def taylorPoly (f : ℝ → ℝ) (n : ℕ) (p x : ℝ) : ℝ :=
 ∑ j ∈ Finset.range (n+1), iteratedDeriv j f p / (j.factorial : ℝ) * (x-p)^j

theorem taylorWithin_eq_poly (f : ℝ → ℝ) (hsmooth : ∀ n : ℕ, ContDiff ℝ n f)
 (n : ℕ) (S : Set ℝ) (hS : UniqueDiffOn ℝ S) {p x : ℝ} (hp : p ∈ S) :
 taylorWithinEval f n S p x = taylorPoly f n p x := by
 rw [taylor_within_apply]
 unfold taylorPoly
 apply Finset.sum_congr rfl
 intro j _
 rw [iteratedDerivWithin_eq_iteratedDeriv hS (hsmooth j).contDiffAt hp]
 simp only [smul_eq_mul]
 ring

theorem taylor_remainder (f : ℝ → ℝ) (hsmooth : ∀ n : ℕ, ContDiff ℝ n f)
 (n : ℕ) {C : ℝ} (hC : ∀ y : ℝ, |iteratedDeriv (n+1) f y| ≤ C) (p x : ℝ) :
 |f x-taylorPoly f n p x| ≤ C * |x-p|^(n+1) / ((n+1).factorial : ℝ) := by
 by_cases hpx : p = x
 · subst x
   have ht := taylorWithin_eq_poly f hsmooth n Set.univ uniqueDiffOn_univ
     (p := p) (x := p) (Set.mem_univ p)
   rw [← ht, taylorWithinEval_self]
   simp
 · have hu : UniqueDiffOn ℝ (uIcc p x) := uniqueDiffOn_Icc (by grind)
   obtain ⟨y, hy, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hpx
     (hsmooth (n+1)).contDiffOn
   rw [taylorWithin_eq_poly f hsmooth n (uIcc p x) hu (left_mem_uIcc)] at he
   rw [he, abs_div, abs_mul, abs_pow, abs_of_nonneg (by positivity : 0 ≤ ((n+1).factorial : ℝ))]
   exact div_le_div_of_nonneg_right
     (mul_le_mul_of_nonneg_right (hC y) (pow_nonneg (abs_nonneg _) _)) (by positivity)

theorem iterated_iterated (f : ℝ → ℝ) (j q : ℕ) :
 iteratedDeriv q (iteratedDeriv j f) = iteratedDeriv (q+j) f := by
 simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

theorem w_contDiff (N : ℕ) (d : ℕ → ℝ) (n : ℕ) : ContDiff ℝ n (w N d) := by
 have he : w N d = fun x => k N d x * k N d x := by
   funext x
   simp only [w, pow_two]
 rw [he]
 exact (k_contDiff N d n).mul (k_contDiff N d n)

theorem w_iterated_contDiff (N : ℕ) (d : ℕ → ℝ) (j n : ℕ) :
 ContDiff ℝ n (iteratedDeriv j (w N d)) := by
 apply contDiff_of_differentiable_iteratedDeriv
 intro q _
 rw [iterated_iterated]
 exact ContDiff.differentiable_iteratedDeriv' (q+j) (w_contDiff N d (q+j+1))

def wSecond : ℝ → ℝ := iteratedDeriv 2 (w 24 d24)

theorem wSecond_remainder (p x : ℝ) :
 |wSecond x-taylorPoly wSecond 13 p x| ≤
   (44/7 : ℝ)^16 * |x-p|^14 / ((14 : ℕ).factorial : ℝ) := by
 apply taylor_remainder wSecond (fun n => w_iterated_contDiff 24 d24 2 n) 13
 intro y
 unfold wSecond
 rw [iterated_iterated]
 exact w24_sixteen_abs_le y

def bernsteinEval (n : ℕ) (β : ℕ → ℝ) (u : ℝ) : ℝ :=
 ∑ j ∈ Finset.range (n+1), β j * (n.choose j : ℝ) * u^j * (1-u)^(n-j)

theorem bernstein_basis_sum (n : ℕ) (u : ℝ) :
 (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)*u^j*(1-u)^(n-j)) = 1 := by
 have h := add_pow u (1-u) n
 have he : u+(1-u) = 1 := by ring
 calc
   _ = ∑ j ∈ Finset.range (n+1), u^j*(1-u)^(n-j)*(n.choose j : ℝ) := by
     apply Finset.sum_congr rfl
     intro j _
     ring
   _ = (u+(1-u))^n := h.symm
   _ = 1 := by rw [he, one_pow]

theorem bernstein_lower {n : ℕ} {β : ℕ → ℝ} {u L : ℝ}
 (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
 (hβ : ∀ j ∈ Finset.range (n+1), L ≤ β j) : L ≤ bernsteinEval n β u := by
 have hsum := bernstein_basis_sum n u
 have hterm : ∀ j ∈ Finset.range (n+1),
   L*((n.choose j : ℝ)*u^j*(1-u)^(n-j)) ≤
     β j*(n.choose j : ℝ)*u^j*(1-u)^(n-j) := by
   intro j hj
   have hu : 0 ≤ 1-u := by linarith
   have hn : 0 ≤ (n.choose j : ℝ)*u^j*(1-u)^(n-j) := by positivity
   have h := mul_le_mul_of_nonneg_right (hβ j hj) hn
   nlinarith only [h]
 have h := Finset.sum_le_sum hterm
 rw [← Finset.mul_sum, hsum, mul_one] at h
 exact h

theorem wSecond_lower_from_Bernstein {a b p radius R L : ℝ} {β : ℕ → ℝ}
 (hab : a < b) (hr : 0 ≤ radius)
 (hrad : ∀ x ∈ Icc a b, |x-p| ≤ radius)
 (hR : (44/7 : ℝ)^16 * radius^14 / ((14 : ℕ).factorial : ℝ) ≤ R)
 (hpoly : ∀ u : ℝ, taylorPoly wSecond 13 p (a+(b-a)*u) = bernsteinEval 13 β u)
 (hβ : ∀ j ∈ Finset.range 14, L+R ≤ β j) :
 ∀ x ∈ Icc a b, L ≤ wSecond x := by
 intro x hx
 let u : ℝ := (x-a)/(b-a)
 have hu0 : 0 ≤ u := div_nonneg (by linarith [hx.1]) (by linarith)
 have hu1 : u ≤ 1 := by
   dsimp [u]
   rw [div_le_one (by linarith : 0 < b-a)]
   linarith [hx.2]
 have hex : a+(b-a)*u = x := by
   dsimp [u]
   field_simp [ne_of_gt (sub_pos.mpr hab)]
   <;> ring
 have hb := bernstein_lower hu0 hu1 hβ
 have hp : L+R ≤ taylorPoly wSecond 13 p x := by
   rw [← hex, hpoly]
   exact hb
 have he := wSecond_remainder p x
 have hpow := pow_le_pow_left₀ (abs_nonneg _) (hrad x hx) 14
 have he' : |wSecond x-taylorPoly wSecond 13 p x| ≤ R := by
   refine he.trans (le_trans ?_ hR)
   exact div_le_div_of_nonneg_right
     (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
 linarith [(abs_le.mp he').1]

#print axioms taylor_remainder
#print axioms wSecond_remainder
#print axioms wSecond_lower_from_Bernstein
end StructuralGoal20261016.WindowConvexityCertificate
end
