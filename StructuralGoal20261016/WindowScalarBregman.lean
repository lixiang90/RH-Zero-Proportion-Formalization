/- SPDX-License-Identifier: Apache-2.0
Actual scalar value/derivative coupling on a bounded-curvature interval.
The interval curvature bounds are explicit; no numerical cover is asserted.
-/
import StructuralGoal20261016.WindowScalarMinorant
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowScalarBregman
open WindowKernel WindowTaylorBridge WindowConvexityCertificate

abbrev f : ℝ → ℝ := w 24 d24

theorem quadratic_upper {a b A p x : ℝ} (hp : p ∈ Icc a b) (hx : x ∈ Icc a b)
    (hsecond : ∀ y ∈ Icc a b, iteratedDeriv 2 f y ≤ 2*A) :
    f x ≤ f p+iteratedDeriv 1 f p*(x-p)+A*(x-p)^2 := by
  by_cases hpx : p = x
  · subst x
    simp
  · have hu : UniqueDiffOn ℝ (uIcc p x) := uniqueDiffOn_Icc (by grind)
    obtain ⟨y,hy,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
      (n := 1) hpx (w_contDiff 24 d24 2).contDiffOn
    rw [taylorWithin_eq_poly f (fun n => w_contDiff 24 d24 n) 1
      (uIcc p x) hu left_mem_uIcc, WindowScalarMinorant.taylor_one] at he
    have hy' : y ∈ Icc a b := by
      have hh := uIoo_subset_uIcc_self hy
      rw [mem_uIcc] at hh
      rcases hh with hh | hh <;> constructor <;> linarith [hp.1,hp.2,hx.1,hx.2]
    have hs := mul_le_mul_of_nonneg_right (hsecond y hy') (sq_nonneg (x-p))
    norm_num at he
    change f x-(f p+deriv f p*(x-p)) = iteratedDeriv 2 f y*(x-p)^2/2 at he
    simp only [iteratedDeriv_one]
    nlinarith only [he,hs]

theorem derivative_increment {a b p x m M : ℝ}
    (hp : p ∈ Icc a b) (hx : x ∈ Icc a b) (hM : m < M)
    (hsecond : ∀ y ∈ Icc a b,
      m ≤ iteratedDeriv 2 f y ∧ iteratedDeriv 2 f y ≤ M) :
    ∃ k : ℝ, m ≤ k ∧ k ≤ M ∧
      iteratedDeriv 1 f x-iteratedDeriv 1 f p = k*(x-p) := by
  by_cases hpx : p = x
  · refine ⟨m,le_rfl,hM.le,?_⟩
    simp [hpx]
  · have hu : UniqueDiffOn ℝ (uIcc p x) := uniqueDiffOn_Icc (by grind)
    obtain ⟨y,hy,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
      (f := iteratedDeriv 1 f) (n := 0) hpx
      (w_iterated_contDiff 24 d24 1 1).contDiffOn
    rw [taylorWithin_eq_poly (iteratedDeriv 1 f)
      (fun n => w_iterated_contDiff 24 d24 1 n) 0 (uIcc p x) hu left_mem_uIcc] at he
    have hy' : y ∈ Icc a b := by
      have hh := uIoo_subset_uIcc_self hy
      rw [mem_uIcc] at hh
      rcases hh with hh | hh <;> constructor <;> linarith [hp.1,hp.2,hx.1,hx.2]
    refine ⟨iteratedDeriv 2 f y,(hsecond y hy').1,(hsecond y hy').2,?_⟩
    simpa [taylorPoly,iterated_iterated,iteratedDeriv_succ] using he

/-- The auxiliary point stays in the same interval, so neither Taylor
estimate requires a curvature hypothesis outside the certified cell. -/
theorem auxiliary_mem {a b p x m M k : ℝ}
    (hp : p ∈ Icc a b) (hx : x ∈ Icc a b) (hM : m < M)
    (hk0 : m ≤ k) (hk1 : k ≤ M)
    (hincrement : iteratedDeriv 1 f x-iteratedDeriv 1 f p = k*(x-p)) :
    x-(iteratedDeriv 1 f x-iteratedDeriv 1 f p-m*(x-p))/(M-m) ∈ Icc a b := by
  let α := (k-m)/(M-m)
  have hL : 0 < M-m := sub_pos.mpr hM
  have ha0 : 0 ≤ α := div_nonneg (sub_nonneg.mpr hk0) hL.le
  have ha1 : α ≤ 1 := (div_le_one hL).mpr (by linarith only [hk1])
  have hz : x-(iteratedDeriv 1 f x-iteratedDeriv 1 f p-m*(x-p))/(M-m) =
      (1-α)*x+α*p := by
    rw [hincrement]
    dsimp [α]
    ring
  rw [hz]
  have hc := (convex_Icc a b) hx hp (sub_nonneg.mpr ha1) ha0
    (by ring : (1-α)+α=1)
  simpa only [smul_eq_mul] using hc

theorem lower {a b p x m M : ℝ}
    (hp : p ∈ Icc a b) (hx : x ∈ Icc a b) (hM : m < M)
    (hsecond : ∀ y ∈ Icc a b,
      m ≤ iteratedDeriv 2 f y ∧ iteratedDeriv 2 f y ≤ M) :
    f p+iteratedDeriv 1 f p*(x-p)+m*(x-p)^2/2+
      (iteratedDeriv 1 f x-iteratedDeriv 1 f p-m*(x-p))^2/(2*(M-m)) ≤ f x := by
  obtain ⟨k,hk0,hk1,hincrement⟩ := derivative_increment hp hx hM hsecond
  let δ := iteratedDeriv 1 f x-iteratedDeriv 1 f p-m*(x-p)
  let z := x-δ/(M-m)
  have hz : z ∈ Icc a b := auxiliary_mem hp hx hM hk0 hk1 hincrement
  have hlo := WindowScalarMinorant.quadratic_tangent (A := m/2) hp hz
    (by
      intro y hy
      change 2*(m/2) ≤ iteratedDeriv 2 f y
      linarith only [(hsecond y hy).1])
  have hup := quadratic_upper (A := M/2) hx hz
    (by intro y hy; linarith only [(hsecond y hy).2])
  have hidentity :
      (f p+iteratedDeriv 1 f p*(z-p)+(m/2)*(z-p)^2)-
        (iteratedDeriv 1 f x*(z-x)+(M/2)*(z-x)^2) =
      f p+iteratedDeriv 1 f p*(x-p)+m*(x-p)^2/2+δ^2/(2*(M-m)) := by
    have hL0 : M-m ≠ 0 := ne_of_gt (sub_pos.mpr hM)
    dsimp [z,δ]
    field_simp [hL0]
    <;> ring
  change f p+iteratedDeriv 1 f p*(x-p)+m*(x-p)^2/2+δ^2/(2*(M-m)) ≤ f x
  rw [← hidentity]
  linarith only [hlo,hup]

theorem square_support (δ L η : ℝ) (hL : 0 < L) :
    η*δ-L*η^2/2 ≤ δ^2/(2*L) := by
  apply (le_div_iff₀ (by positivity : 0 < 2*L)).mpr
  nlinarith only [sq_nonneg (δ-L*η)]

/-- Any real support parameter is valid; rational parameters can be used
directly by the existing rational moment-row interpreter. -/
theorem affine_lower {a b p x m M : ℝ} (η : ℝ)
    (hp : p ∈ Icc a b) (hx : x ∈ Icc a b) (hM : m < M)
    (hsecond : ∀ y ∈ Icc a b,
      m ≤ iteratedDeriv 2 f y ∧ iteratedDeriv 2 f y ≤ M) :
    f p+iteratedDeriv 1 f p*(x-p)+m*(x-p)^2/2+
      η*(iteratedDeriv 1 f x-iteratedDeriv 1 f p-m*(x-p))-
      (M-m)*η^2/2 ≤ f x := by
  have hb := lower hp hx hM hsecond
  have hs := square_support
    (iteratedDeriv 1 f x-iteratedDeriv 1 f p-m*(x-p)) (M-m) η (sub_pos.mpr hM)
  linarith only [hb,hs]

set_option pp.fullNames true
#print axioms quadratic_upper
#print axioms derivative_increment
#print axioms auxiliary_mem
#print axioms lower
#print axioms square_support
#print axioms affine_lower
end StructuralGoal20261016.WindowScalarBregman
end
