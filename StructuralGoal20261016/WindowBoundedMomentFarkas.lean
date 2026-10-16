/- SPDX-License-Identifier: Apache-2.0
Integer Farkas combinations on actual bounded lifted variables. The common
box scale is explicit: L/scale <= z <= U/scale. Residual coefficients need
not vanish; their exact box support is paid in the strict separation test.
The product/RLT/Gram lemmas below concern genuine products of actual values,
so no independent feasibility assumption on an abstract moment matrix is used.
-/
import StructuralGoal20261016.WindowLiftedFarkas
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowBoundedMomentFarkas

structure Row (m : ℕ) where
  coeff : Fin m → ℤ
  bound : ℤ

def eval {m : ℕ} (row : Row m) (z : Fin m → ℝ) : ℝ :=
  ∑ j, (row.coeff j:ℝ)*z j

def aggregate {n m : ℕ} (rows : Fin n → Row m) (mu : Fin n → ℤ) : Row m where
  coeff := fun j => ∑ i, mu i*(rows i).coeff j
  bound := ∑ i, mu i*(rows i).bound

theorem aggregate_eval {n m : ℕ} (rows : Fin n → Row m) (mu : Fin n → ℤ)
    (z : Fin m → ℝ) :
    eval (aggregate rows mu) z = ∑ i, (mu i:ℝ)*eval (rows i) z := by
  change (∑ j, ((∑ i, mu i*(rows i).coeff j:ℤ):ℝ)*z j) = _
  simpa only [eval] using WindowLiftedFarkas.weighted_dot
    (fun i j => (rows i).coeff j) mu z

theorem aggregate_valid {n m : ℕ} (rows : Fin n → Row m) (mu : Fin n → ℤ)
    (z : Fin m → ℝ) (hmu : ∀ i, 0 ≤ mu i)
    (hrows : ∀ i, eval (rows i) z ≤ ((rows i).bound:ℝ)) :
    eval (aggregate rows mu) z ≤ ((aggregate rows mu).bound:ℝ) := by
  rw [aggregate_eval]
  change _ ≤ ((∑ i, mu i*(rows i).bound:ℤ):ℝ)
  push_cast
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (hrows i) (by exact_mod_cast hmu i)

def supportLower {m : ℕ} (coeff L U : Fin m → ℤ) : ℤ :=
  ∑ j, min (coeff j*L j) (coeff j*U j)

theorem support_lower {m : ℕ} (coeff L U : Fin m → ℤ) (z : Fin m → ℝ)
    (hz : ∀ j, (L j:ℝ) ≤ z j ∧ z j ≤ (U j:ℝ)) :
    (supportLower coeff L U:ℝ) ≤ ∑ j, (coeff j:ℝ)*z j := by
  unfold supportLower
  rw [Int.cast_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hc : (0:ℤ) ≤ coeff j
  · have hcR : (0:ℝ) ≤ (coeff j:ℝ) := by exact_mod_cast hc
    have hmin : ((min (coeff j*L j) (coeff j*U j):ℤ):ℝ) ≤
        (coeff j:ℝ)*(L j:ℝ) := by exact_mod_cast min_le_left (coeff j*L j) (coeff j*U j)
    exact hmin.trans (mul_le_mul_of_nonneg_left (hz j).1 hcR)
  · have hcR : (coeff j:ℝ) ≤ 0 := by exact_mod_cast le_of_not_ge hc
    have hmin : ((min (coeff j*L j) (coeff j*U j):ℤ):ℝ) ≤
        (coeff j:ℝ)*(U j:ℝ) := by exact_mod_cast min_le_right (coeff j*L j) (coeff j*U j)
    exact hmin.trans (mul_le_mul_of_nonpos_left (hz j).2 hcR)

theorem scaled_support_lower {m : ℕ} (scale : ℤ) (coeff L U : Fin m → ℤ)
    (hs : 0 < scale) (z : Fin m → ℝ)
    (hz : ∀ j, (L j:ℝ)/(scale:ℝ) ≤ z j ∧ z j ≤ (U j:ℝ)/(scale:ℝ)) :
    (supportLower coeff L U:ℝ) ≤ (scale:ℝ)*(∑ j, (coeff j:ℝ)*z j) := by
  have hsR : (0:ℝ) < (scale:ℝ) := by exact_mod_cast hs
  have hbox : ∀ j, (L j:ℝ) ≤ (scale:ℝ)*z j ∧ (scale:ℝ)*z j ≤ (U j:ℝ) := by
    intro j
    constructor
    · simpa only [mul_comm] using (div_le_iff₀ hsR).mp (hz j).1
    · simpa only [mul_comm] using (le_div_iff₀ hsR).mp (hz j).2
  have h := support_lower coeff L U (fun j => (scale:ℝ)*z j) hbox
  calc
    (supportLower coeff L U:ℝ) ≤ ∑ j, (coeff j:ℝ)*((scale:ℝ)*z j) := h
    _ = (scale:ℝ)*(∑ j, (coeff j:ℝ)*z j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

def check {n m : ℕ} (scale : ℤ) (rows : Fin n → Row m) (mu : Fin n → ℤ)
    (L U : Fin m → ℤ) : Bool := decide (
  0 < scale ∧ (∀ i, 0 ≤ mu i) ∧
    scale*(aggregate rows mu).bound < supportLower (aggregate rows mu).coeff L U)

theorem exclude {n m : ℕ} {scale : ℤ} (rows : Fin n → Row m) (mu : Fin n → ℤ)
    (L U : Fin m → ℤ) (hc : check scale rows mu L U = true)
    (z : Fin m → ℝ)
    (hz : ∀ j, (L j:ℝ)/(scale:ℝ) ≤ z j ∧ z j ≤ (U j:ℝ)/(scale:ℝ))
    (hrows : ∀ i, eval (rows i) z ≤ ((rows i).bound:ℝ)) : False := by
  have hh : 0 < scale ∧ (∀ i, 0 ≤ mu i) ∧
      scale*(aggregate rows mu).bound < supportLower (aggregate rows mu).coeff L U :=
    of_decide_eq_true hc
  have hsR : (0:ℝ) < (scale:ℝ) := by exact_mod_cast hh.1
  have hstrict : (scale:ℝ)*((aggregate rows mu).bound:ℝ) <
      (supportLower (aggregate rows mu).coeff L U:ℝ) := by exact_mod_cast hh.2.2
  have hv := aggregate_valid rows mu z hh.2.1 hrows
  have hl := scaled_support_lower scale (aggregate rows mu).coeff L U hh.1 z hz
  have hu := mul_le_mul_of_nonneg_left hv (le_of_lt hsR)
  change (supportLower (aggregate rows mu).coeff L U:ℝ) ≤
    (scale:ℝ)*eval (aggregate rows mu) z at hl
  linarith

theorem mul_between {l u x : ℝ} (hx : l ≤ x ∧ x ≤ u) (c : ℝ) :
    min (c*l) (c*u) ≤ c*x ∧ c*x ≤ max (c*l) (c*u) := by
  by_cases hc : 0 ≤ c
  · have horder := mul_le_mul_of_nonneg_left (hx.1.trans hx.2) hc
    rw [min_eq_left horder,max_eq_right horder]
    exact ⟨mul_le_mul_of_nonneg_left hx.1 hc,mul_le_mul_of_nonneg_left hx.2 hc⟩
  · have hc' : c ≤ 0 := le_of_not_ge hc
    have horder := mul_le_mul_of_nonpos_left (hx.1.trans hx.2) hc'
    rw [min_eq_right horder,max_eq_left horder]
    exact ⟨mul_le_mul_of_nonpos_left hx.2 hc',mul_le_mul_of_nonpos_left hx.1 hc'⟩

theorem product_enclosure {l u L U x y : ℝ}
    (hx : l ≤ x ∧ x ≤ u) (hy : L ≤ y ∧ y ≤ U) :
    min (min (L*l) (L*u)) (min (U*l) (U*u)) ≤ x*y ∧
      x*y ≤ max (max (L*l) (L*u)) (max (U*l) (U*u)) := by
  have hL : min (L*l) (L*u) ≤ x*L ∧ x*L ≤ max (L*l) (L*u) := by
    simpa only [mul_comm] using mul_between hx L
  have hU : min (U*l) (U*u) ≤ x*U ∧ x*U ≤ max (U*l) (U*u) := by
    simpa only [mul_comm] using mul_between hx U
  have hxy := mul_between hy x
  constructor
  · exact (le_min ((min_le_left _ _).trans hL.1)
      ((min_le_right _ _).trans hU.1)).trans hxy.1
  · exact hxy.2.trans (max_le (hL.2.trans (le_max_left _ _))
      (hU.2.trans (le_max_right _ _)))

theorem mccormick_lower_lower {l L x y : ℝ} (hx : l ≤ x) (hy : L ≤ y) :
    l*y+L*x-l*L ≤ x*y := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]

theorem mccormick_upper_upper {u U x y : ℝ} (hx : x ≤ u) (hy : y ≤ U) :
    u*y+U*x-u*U ≤ x*y := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]

theorem mccormick_upper_lower {u L x y : ℝ} (hx : x ≤ u) (hy : L ≤ y) :
    x*y ≤ u*y+L*x-u*L := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]

theorem mccormick_lower_upper {l U x y : ℝ} (hx : l ≤ x) (hy : y ≤ U) :
    x*y ≤ l*y+U*x-l*U := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]

theorem product_sum {m : ℕ} (a z : Fin m → ℝ) (j : Fin m) :
    (∑ k, a k*(z j*z k)) = z j*(∑ k, a k*z k) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem rlt_lower {m : ℕ} (a z : Fin m → ℝ) (j : Fin m) {b L : ℝ}
    (hrow : (∑ k, a k*z k) ≤ b) (hz : L ≤ z j) :
    (∑ k, a k*(z j*z k))-b*z j-L*(∑ k, a k*z k) ≤ -L*b := by
  rw [product_sum]
  nlinarith [mul_nonneg (sub_nonneg.mpr hrow) (sub_nonneg.mpr hz)]

theorem rlt_upper {m : ℕ} (a z : Fin m → ℝ) (j : Fin m) {b U : ℝ}
    (hrow : (∑ k, a k*z k) ≤ b) (hz : z j ≤ U) :
    -(∑ k, a k*(z j*z k))+b*z j+U*(∑ k, a k*z k) ≤ U*b := by
  rw [product_sum]
  nlinarith [mul_nonneg (sub_nonneg.mpr hrow) (sub_nonneg.mpr hz)]

theorem multiply_eq {m : ℕ} (a z : Fin m → ℝ) (j : Fin m) {b : ℝ}
    (hrow : (∑ k, a k*z k) = b) :
    (∑ k, a k*(z j*z k)) = b*z j := by
  rw [product_sum,hrow]
  ring

theorem gram_quadratic {m : ℕ} (v z : Fin m → ℝ) :
    (∑ i, ∑ j, v i*v j*(z i*z j)) = (∑ i, v i*z i)^2 := by
  rw [pow_two,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem gram_psd {m : ℕ} (v z : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, v i*v j*(z i*z j) := by
  rw [gram_quadratic]
  exact sq_nonneg _

set_option pp.fullNames true
#print axioms aggregate_eval
#print axioms aggregate_valid
#print axioms scaled_support_lower
#print axioms exclude
#print axioms product_enclosure
#print axioms mccormick_lower_lower
#print axioms mccormick_upper_upper
#print axioms mccormick_upper_lower
#print axioms mccormick_lower_upper
#print axioms rlt_lower
#print axioms rlt_upper
#print axioms multiply_eq
#print axioms gram_psd
end StructuralGoal20261016.WindowBoundedMomentFarkas
end
