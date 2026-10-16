/- SPDX-License-Identifier: Apache-2.0
Outward integer rounding of rational inequalities on signed finite boxes.
Every coefficient error is paid using max(abs lower,abs upper). The scale
is positive and explicit; coefficients and interval endpoints may be signed.
This module supplies no numerical certificate or actual moment exclusion.
-/
import StructuralGoal20261016.WindowBoundedMomentFarkas
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowMomentRounding
open WindowBoundedMomentFarkas (Row eval)

def rationalEval {m : ℕ} (a : Fin m → ℚ) (x : Fin m → ℝ) : ℝ :=
  ∑ j, (a j:ℝ)*x j

def errorPayment {m : ℕ} (scale : ℤ) (a : Fin m → ℚ)
    (C : Fin m → ℤ) (lower upper : Fin m → ℚ) : ℚ :=
  ∑ j, |a j-(C j:ℚ)/(scale:ℚ)| * max |lower j| |upper j|

def check {m : ℕ} (scale : ℤ) (a : Fin m → ℚ) (B : ℚ)
    (row : Row m) (lower upper : Fin m → ℚ) : Bool := decide (
  0 < scale ∧ B+errorPayment scale a row.coeff lower upper ≤
    (row.bound:ℚ)/(scale:ℚ))

theorem abs_box {l u x : ℝ} (hx : l ≤ x ∧ x ≤ u) :
    |x| ≤ max |l| |u| := by
  apply abs_le.mpr
  constructor
  · exact (neg_le_neg (le_max_left |l| |u|)).trans ((neg_abs_le l).trans hx.1)
  · exact hx.2.trans ((le_abs_self u).trans (le_max_right |l| |u|))

theorem payment_cast {m : ℕ} (scale : ℤ) (a : Fin m → ℚ)
    (C : Fin m → ℤ) (lower upper : Fin m → ℚ) :
    (errorPayment scale a C lower upper:ℝ) =
      ∑ j, |(a j:ℝ)-(C j:ℝ)/(scale:ℝ)| *
        max |(lower j:ℝ)| |(upper j:ℝ)| := by
  unfold errorPayment
  push_cast <;> rfl

theorem row_error_upper {m : ℕ} (scale : ℤ) (a : Fin m → ℚ)
    (C : Fin m → ℤ) (lower upper : Fin m → ℚ) (x : Fin m → ℝ)
    (hx : ∀ j, (lower j:ℝ) ≤ x j ∧ x j ≤ (upper j:ℝ)) :
    (∑ j, ((C j:ℝ)/(scale:ℝ)-(a j:ℝ))*x j) ≤
      (errorPayment scale a C lower upper:ℝ) := by
  rw [payment_cast]
  apply Finset.sum_le_sum
  intro j _
  calc
    ((C j:ℝ)/(scale:ℝ)-(a j:ℝ))*x j ≤
        |((C j:ℝ)/(scale:ℝ)-(a j:ℝ))*x j| := le_abs_self _
    _ = |(a j:ℝ)-(C j:ℝ)/(scale:ℝ)| * |x j| := by
      rw [abs_mul,abs_sub_comm]
    _ ≤ |(a j:ℝ)-(C j:ℝ)/(scale:ℝ)| *
        max |(lower j:ℝ)| |(upper j:ℝ)| :=
      mul_le_mul_of_nonneg_left (abs_box (hx j)) (abs_nonneg _)

theorem valid {m : ℕ} (scale : ℤ) (a : Fin m → ℚ) (B : ℚ)
    (row : Row m) (lower upper : Fin m → ℚ)
    (hc : check scale a B row lower upper = true)
    (x : Fin m → ℝ)
    (hx : ∀ j, (lower j:ℝ) ≤ x j ∧ x j ≤ (upper j:ℝ))
    (hrow : rationalEval a x ≤ (B:ℝ)) :
    eval row x ≤ (row.bound:ℝ) := by
  have hh : 0 < scale ∧ B+errorPayment scale a row.coeff lower upper ≤
      (row.bound:ℚ)/(scale:ℚ) := of_decide_eq_true hc
  have hsR : (0:ℝ) < (scale:ℝ) := by exact_mod_cast hh.1
  have hbudget : (B:ℝ)+(errorPayment scale a row.coeff lower upper:ℝ) ≤
      (row.bound:ℝ)/(scale:ℝ) := by
    exact_mod_cast hh.2
  have herror := row_error_upper scale a row.coeff lower upper x hx
  have hsplit :
      (∑ j, ((row.coeff j:ℝ)/(scale:ℝ))*x j) =
      rationalEval a x+(∑ j, ((row.coeff j:ℝ)/(scale:ℝ)-(a j:ℝ))*x j) := by
    unfold rationalEval
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hbounded : (∑ j, ((row.coeff j:ℝ)/(scale:ℝ))*x j) ≤
      (row.bound:ℝ)/(scale:ℝ) := by
    rw [hsplit]
    exact (add_le_add hrow herror).trans hbudget
  have hdivide : (∑ j, ((row.coeff j:ℝ)/(scale:ℝ))*x j) =
      eval row x/(scale:ℝ) := by
    unfold eval
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hdivide] at hbounded
  calc
    eval row x ≤ ((row.bound:ℝ)/(scale:ℝ))*(scale:ℝ) :=
      (div_le_iff₀ hsR).mp hbounded
    _ = (row.bound:ℝ) := by field_simp [ne_of_gt hsR]

set_option pp.fullNames true
#print axioms abs_box
#print axioms payment_cast
#print axioms row_error_upper
#print axioms valid
end StructuralGoal20261016.WindowMomentRounding
end
