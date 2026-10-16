/- SPDX-License-Identifier: Apache-2.0
Optimizer-free soundness of affine energy mixtures and directed flow bounds.
The LP only selects nonnegative rational data; exact balance, capacities and
edge inequalities suffice. No optimality or solver correctness is assumed.
-/
import Mathlib.Tactic
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Finset
namespace StructuralGoal20261016.AffineFlowCertificate

theorem scalar_mixture_le {ι : Type*} [Fintype ι]
    (lam line : ι → ℝ) (a w : ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hline : ∀ i, line i ≤ w)
    (hmass : ∑ i, lam i ≤ a) (hw : 0 ≤ w) :
    (∑ i, lam i * line i) ≤ a * w := by
  calc
    (∑ i, lam i * line i) ≤ ∑ i, lam i * w :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hline i) (hlam i))
    _ = (∑ i, lam i) * w := (Finset.sum_mul _ _ _).symm
    _ ≤ a * w := mul_le_mul_of_nonneg_right hmass hw

theorem energy_mixture_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (lam line : ι → κ → ℝ) (a w : ι → ℝ) (pressure : ℝ)
    (hlam : ∀ i j, 0 ≤ lam i j) (hline : ∀ i j, line i j ≤ w i)
    (hmass : ∀ i, ∑ j, lam i j ≤ a i) (hw : ∀ i, 0 ≤ w i) :
    pressure + ∑ i, ∑ j, lam i j * line i j ≤
      pressure + ∑ i, a i * w i := by
  exact add_le_add le_rfl (Finset.sum_le_sum fun i _ =>
    scalar_mixture_le (lam i) (line i) (a i) (w i)
      (hlam i) (hline i) (hmass i) (hw i))

theorem flow_balance_identity {ι : Type*} [Fintype ι]
    (flow : ι → ι → ℝ) (x coefficient : ι → ℝ)
    (hbalance : ∀ i, (∑ j, flow i j) - (∑ j, flow j i) = coefficient i) :
    (∑ i, coefficient i * x i) =
      ∑ i, ∑ j, flow i j * (x i - x j) := by
  simp_rw [← hbalance, sub_mul, Finset.sum_mul, mul_sub]
  simp_rw [Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

theorem flow_lower_bound {ι : Type*} [Fintype ι]
    (flow upper : ι → ι → ℝ) (x coefficient : ι → ℝ)
    (hflow : ∀ i j, 0 ≤ flow i j)
    (hedge : ∀ i j, x j - x i ≤ upper i j)
    (hbalance : ∀ i, (∑ j, flow i j) - (∑ j, flow j i) = coefficient i) :
    -(∑ i, ∑ j, flow i j * upper i j) ≤ ∑ i, coefficient i * x i := by
  rw [flow_balance_identity flow x coefficient hbalance]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro j _
  have h := mul_le_mul_of_nonneg_left (hedge i j) (hflow i j)
  nlinarith

set_option pp.fullNames true
#print axioms scalar_mixture_le
#print axioms energy_mixture_le
#print axioms flow_balance_identity
#print axioms flow_lower_bound
end StructuralGoal20261016.AffineFlowCertificate
end
