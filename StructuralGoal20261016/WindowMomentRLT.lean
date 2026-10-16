/- SPDX-License-Identifier: Apache-2.0
Grouped RLT multipliers. Nonnegative combinations of the factors (1±y_s)
are stored as A+Σb_s*y_s. The absolute-sum condition proves nonnegativity
on the actual normalized gap box. This module makes no exclusion claim.
-/
import StructuralGoal20261016.WindowMomentLayout
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowMomentRLT

def multiplier {n : ℕ} (A : ℝ) (b y : Fin n → ℝ) : ℝ := A+∑ s, b s*y s

theorem multiplier_nonneg {n : ℕ} {A : ℝ} {b y : Fin n → ℝ}
    (hA : (∑ s, |b s|) ≤ A) (hy : ∀ s, -1 ≤ y s ∧ y s ≤ 1) :
    0 ≤ multiplier A b y := by
  have ht : ∀ s, -|b s| ≤ b s*y s := by
    intro s
    have h := abs_mul (b s) (y s)
    have hu : |b s*y s| ≤ |b s| := by
      rw [h]
      exact (mul_le_mul_of_nonneg_left (abs_le.mpr (hy s)) (abs_nonneg _)).trans_eq (mul_one _)
    exact (abs_le.mp hu).1
  have hs := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => ht s)
  rw [Finset.sum_neg_distrib] at hs
  unfold multiplier
  linarith

theorem grouped_nonpos {n : ℕ} {A value bound : ℝ} {b y : Fin n → ℝ}
    (hA : (∑ s, |b s|) ≤ A) (hy : ∀ s, -1 ≤ y s ∧ y s ≤ 1)
    (hrow : value ≤ bound) :
    (value-bound)*multiplier A b y ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hrow) (multiplier_nonneg hA hy)

theorem actual_nonpos {A value bound : ℝ} {b center radius g : Fin 9 → ℝ}
    (hA : (∑ s, |b s|) ≤ A) (hr : ∀ s, 0 < radius s)
    (hg : ∀ s, center s-radius s ≤ g s ∧ g s ≤ center s+radius s)
    (hrow : value ≤ bound) :
    (value-bound)*multiplier A b (WindowMomentLayout.normalized center radius g) ≤ 0 :=
  grouped_nonpos hA (fun s => WindowMomentLayout.normalized_bounds s (hr s) (hg s)) hrow

theorem factor_compression {n : ℕ} (muPlus muMinus : Fin n → ℝ) (base : ℝ)
    (hp : ∀ s, 0 ≤ muPlus s) (hm : ∀ s, 0 ≤ muMinus s) (hb : 0 ≤ base) :
    (∑ s, |muPlus s-muMinus s|) ≤ base+∑ s, (muPlus s+muMinus s) := by
  have hs : (∑ s, |muPlus s-muMinus s|) ≤ ∑ s, (muPlus s+muMinus s) := by
    apply Finset.sum_le_sum
    intro s _
    apply abs_le.mpr
    constructor <;> linarith [hp s,hm s]
  linarith

theorem compression_identity {n : ℕ} (muPlus muMinus y : Fin n → ℝ) (base : ℝ) :
    base+∑ s, (muPlus s*(1+y s)+muMinus s*(1-y s)) =
      multiplier (base+∑ s, (muPlus s+muMinus s))
        (fun s => muPlus s-muMinus s) y := by
  unfold multiplier
  rw [add_assoc,← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  ring

set_option pp.fullNames true
#print axioms multiplier_nonneg
#print axioms grouped_nonpos
#print axioms actual_nonpos
#print axioms factor_compression
#print axioms compression_identity
end StructuralGoal20261016.WindowMomentRLT
end
