/-
SPDX-License-Identifier: Apache-2.0

Finite arithmetic certificates for affine lower bounds. A numerical optimizer
may discover nonnegative flows or mixtures; the theorems below require their
exact constraints and never trust the optimizer. No new zeta bound is stated.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset
open scoped BigOperators

namespace StructuralResearch20261016.AffineFlow

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def divergence (F : ι → ι → ℝ) (i : ι) : ℝ :=
  (∑ j, F i j) - (∑ j, F j i)

def flowCost (F U : ι → ι → ℝ) : ℝ := ∑ i, ∑ j, F i j * U i j

/-- Discrete integration by parts: incoming mass is reindexed, not discarded. -/
theorem divergence_pairing (F : ι → ι → ℝ) (x : ι → ℝ) :
    (∑ i, divergence F i * x i) = ∑ i, ∑ j, F i j * (x i - x j) := by
  simp only [divergence, sub_mul, mul_sub, sum_sub_distrib, sum_mul]
  congr 1
  rw [sum_comm]

/-- Exact nonnegative-flow duality for finite difference constraints.
Neither `U` nor the coordinates are required to be nonnegative. -/
theorem lower_of_flow (F U : ι → ι → ℝ) (x : ι → ℝ)
    (hF : ∀ i j, 0 ≤ F i j)
    (hU : ∀ i j, x j - x i ≤ U i j) :
    -flowCost F U ≤ ∑ i, divergence F i * x i := by
  rw [divergence_pairing]
  calc
    -flowCost F U = ∑ i, ∑ j, -(F i j * U i j) := by
      simp only [flowCost, sum_neg_distrib]
    _ ≤ ∑ i, ∑ j, F i j * (x i - x j) := by
      refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
      have h := mul_le_mul_of_nonneg_left (hU i j) (hF i j)
      nlinarith only [h]

theorem lower_of_balanced_flow (F U : ι → ι → ℝ) (x c : ι → ℝ)
    (hF : ∀ i j, 0 ≤ F i j)
    (hU : ∀ i j, x j - x i ≤ U i j)
    (hbalance : ∀ i, c i = (∑ j, F i j) - (∑ j, F j i)) :
    -flowCost F U ≤ ∑ i, c i * x i := by
  simpa only [hbalance, divergence] using lower_of_flow F U x hF hU

/-- A solver-independent affine certificate: the exact flow cost pays the
linear part of an independently justified lower bound on `E`. -/
theorem target_le_of_flow (F U : ι → ι → ℝ) (x c : ι → ℝ)
    (hF : ∀ i j, 0 ≤ F i j)
    (hU : ∀ i j, x j - x i ≤ U i j)
    (hbalance : ∀ i, c i = (∑ j, F i j) - (∑ j, F j i))
    {constant target E : ℝ}
    (hE : constant + ∑ i, c i * x i ≤ E)
    (htarget : target ≤ constant - flowCost F U) : target ≤ E := by
  linarith [lower_of_balanced_flow F U x c hF hU hbalance]

/-- Unused nonnegative kernel mass may be dropped. The minorants themselves
can be negative, as happens with affine tangent bounds. -/
theorem weighted_minorants (f a : ι → ℝ) (lam lower : ι → κ → ℝ)
    (hf : ∀ i, 0 ≤ f i)
    (hlam : ∀ i j, 0 ≤ lam i j)
    (hmass : ∀ i, ∑ j, lam i j ≤ a i)
    (hlower : ∀ i j, lower i j ≤ f i) :
    (∑ i, ∑ j, lam i j * lower i j) ≤ ∑ i, a i * f i := by
  calc
    (∑ i, ∑ j, lam i j * lower i j) ≤ ∑ i, ∑ j, lam i j * f i :=
      sum_le_sum fun i _ => sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hlower i j) (hlam i j)
    _ = ∑ i, (∑ j, lam i j) * f i := by simp only [sum_mul]
    _ ≤ ∑ i, a i * f i :=
      sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hmass i) (hf i)

end StructuralResearch20261016.AffineFlow
