/- SPDX-License-Identifier: Apache-2.0
Exact componentwise sums, additions and scalings of rational moment forms.
The actual 464-variable evaluator is linear; no rounding or numerical
certificate is introduced by this module.
-/
import StructuralGoal20261016.WindowMomentPolynomial
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowMomentFormSum
open WindowMomentPolynomial

def scale (c : ℚ) (a : RatForm) : RatForm where
  gap := fun r => c*a.gap r
  scalar := fun e => c*a.scalar e
  h := fun e => c*a.h e
  q := fun r e => c*a.q r e
  bound := c*a.bound

def add (a b : RatForm) : RatForm where
  gap := fun r => a.gap r+b.gap r
  scalar := fun e => a.scalar e+b.scalar e
  h := fun e => a.h e+b.h e
  q := fun r e => a.q r e+b.q r e
  bound := a.bound+b.bound

def sumForms {n : ℕ} (rows : Fin n → RatForm) : RatForm where
  gap := fun r => ∑ i, (rows i).gap r
  scalar := fun e => ∑ i, (rows i).scalar e
  h := fun e => ∑ i, (rows i).h e
  q := fun r e => ∑ i, (rows i).q r e
  bound := ∑ i, (rows i).bound

theorem flatten_scale (c : ℚ) (a : RatForm) (j : Fin 464) :
    flatten (scale c a) j = c*flatten a j := by
  unfold flatten
  cases hd : decode j with
  | inl r => rfl
  | inr b =>
    cases b with
    | inl e => rfl
    | inr b =>
      cases b with
      | inl e => rfl
      | inr p => rfl

theorem flatten_add (a b : RatForm) (j : Fin 464) :
    flatten (add a b) j = flatten a j+flatten b j := by
  unfold flatten
  cases hd : decode j with
  | inl r => rfl
  | inr c =>
    cases c with
    | inl e => rfl
    | inr c =>
      cases c with
      | inl e => rfl
      | inr p => rfl

theorem flatten_sum {n : ℕ} (rows : Fin n → RatForm) (j : Fin 464) :
    flatten (sumForms rows) j = ∑ i, flatten (rows i) j := by
  unfold flatten
  cases hd : decode j with
  | inl r => rfl
  | inr b =>
    cases b with
    | inl e => rfl
    | inr b =>
      cases b with
      | inl e => rfl
      | inr p => rfl

theorem eval_scale (c : ℚ) (a : RatForm) (center radius g : Fin 9 → ℝ) :
    eval (scale c a) center radius g = (c:ℝ)*eval a center radius g := by
  unfold WindowMomentPolynomial.eval WindowMomentRounding.rationalEval
  simp only [flatten_scale,Rat.cast_mul,mul_assoc,Finset.mul_sum]

theorem eval_add (a b : RatForm) (center radius g : Fin 9 → ℝ) :
    eval (add a b) center radius g = eval a center radius g+eval b center radius g := by
  unfold WindowMomentPolynomial.eval WindowMomentRounding.rationalEval
  simp only [flatten_add,Rat.cast_add,add_mul,Finset.sum_add_distrib]

theorem eval_sum {n : ℕ} (rows : Fin n → RatForm) (center radius g : Fin 9 → ℝ) :
    eval (sumForms rows) center radius g = ∑ i, eval (rows i) center radius g := by
  unfold WindowMomentPolynomial.eval WindowMomentRounding.rationalEval
  simp_rw [flatten_sum,Rat.cast_sum,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem bound_scale_cast (c : ℚ) (a : RatForm) :
    ((scale c a).bound:ℝ) = (c:ℝ)*(a.bound:ℝ) := by
  simp only [scale,Rat.cast_mul]

theorem bound_add_cast (a b : RatForm) :
    ((add a b).bound:ℝ) = (a.bound:ℝ)+(b.bound:ℝ) := by
  simp only [add,Rat.cast_add]

theorem bound_sum_cast {n : ℕ} (rows : Fin n → RatForm) :
    ((sumForms rows).bound:ℝ) = ∑ i, ((rows i).bound:ℝ) := by
  simp only [sumForms,Rat.cast_sum]

theorem scale_valid (c : ℚ) (a : RatForm) (center radius g : Fin 9 → ℝ)
    (hc : 0 ≤ c) (ha : eval a center radius g ≤ (a.bound:ℝ)) :
    eval (scale c a) center radius g ≤ ((scale c a).bound:ℝ) := by
  rw [eval_scale,bound_scale_cast]
  exact mul_le_mul_of_nonneg_left ha (Rat.cast_nonneg.mpr hc)

theorem add_valid (a b : RatForm) (center radius g : Fin 9 → ℝ)
    (ha : eval a center radius g ≤ (a.bound:ℝ))
    (hb : eval b center radius g ≤ (b.bound:ℝ)) :
    eval (add a b) center radius g ≤ ((add a b).bound:ℝ) := by
  rw [eval_add,bound_add_cast]
  exact add_le_add ha hb

theorem sum_valid {n : ℕ} (rows : Fin n → RatForm) (center radius g : Fin 9 → ℝ)
    (hrows : ∀ i, eval (rows i) center radius g ≤ ((rows i).bound:ℝ)) :
    eval (sumForms rows) center radius g ≤ ((sumForms rows).bound:ℝ) := by
  rw [eval_sum,bound_sum_cast]
  exact Finset.sum_le_sum (fun i _ => hrows i)

theorem add_valid_of_lt_right (a b : RatForm) (center radius g : Fin 9 → ℝ)
    (ha : eval a center radius g ≤ (a.bound:ℝ))
    (hb : eval b center radius g < (b.bound:ℝ)) :
    eval (add a b) center radius g < ((add a b).bound:ℝ) := by
  rw [eval_add,bound_add_cast]
  exact add_lt_add_of_le_of_lt ha hb

set_option pp.fullNames true
#print axioms flatten_scale
#print axioms flatten_add
#print axioms flatten_sum
#print axioms eval_scale
#print axioms eval_add
#print axioms eval_sum
#print axioms scale_valid
#print axioms add_valid
#print axioms sum_valid
#print axioms add_valid_of_lt_right
end StructuralGoal20261016.WindowMomentFormSum
end
