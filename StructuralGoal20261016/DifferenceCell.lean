/- SPDX-License-Identifier: Apache-2.0
Exact difference-cell geometry for the minimizer-cover checker.
A branch adds one directed edge and performs its full single-edge closure.
All soundness statements concern actual real potentials.
-/
import StructuralGoal20261016.FlowBasisCodec
set_option Elab.async false
set_option maxHeartbeats 0
namespace StructuralGoal20261016.DifferenceCell

abbrev Cell (n : ℕ) := Fin n → Fin n → ℤ

def Contains {n : ℕ} (cell : Cell n) (x : Fin n → ℝ) : Prop :=
  ∀ i j, x j - x i ≤ (cell i j : ℝ)

def addEdge {n : ℕ} (cell : Cell n) (i j : Fin n) (q : ℤ) : Cell n :=
  fun a b => min (cell a b) (cell a i + q + cell j b)

theorem addEdge_sound {n : ℕ} {cell : Cell n} {x : Fin n → ℝ}
    (hcell : Contains cell x) (i j : Fin n) (q : ℤ)
    (hcut : x j - x i ≤ (q : ℝ)) : Contains (addEdge cell i j q) x := by
  intro a b
  change x b-x a ≤ ((min (cell a b) (cell a i+q+cell j b) : ℤ) : ℝ)
  rcases le_total (cell a b) (cell a i+q+cell j b) with h | h
  · rw [min_eq_left h]
    exact hcell a b
  · rw [min_eq_right h]
    push_cast
    have h1 := hcell a i
    have h2 := hcell j b
    linarith

theorem split_sound {n : ℕ} {cell : Cell n} {x : Fin n → ℝ}
    (hcell : Contains cell x) (i j : Fin n) (q : ℤ) :
    Contains (addEdge cell i j q) x ∨ Contains (addEdge cell j i (-q)) x := by
  by_cases h : x j-x i ≤ (q : ℝ)
  · exact Or.inl (addEdge_sound hcell i j q h)
  · apply Or.inr
    apply addEdge_sound hcell j i (-q)
    push_cast
    linarith

theorem negative_diagonal_empty {n : ℕ} {cell : Cell n} (i : Fin n)
    (hnegative : cell i i < 0) : ∀ x, ¬ Contains cell x := by
  intro x hx
  have h := hx i i
  have hneg : (cell i i : ℝ) < 0 := by exact_mod_cast hnegative
  linarith

theorem affine_flow_bound {n : ℕ} (cell : Cell n) (x : Fin n → ℝ)
    (hcell : Contains cell x) (edges : List FlowBasisCodec.Edge)
    (coefficient : Fin n → ℤ) (intercept target : ℤ)
    (checked : FlowBasisCodec.checkBasis edges cell coefficient intercept target = true) :
    (target : ℝ) ≤ (intercept : ℝ) + ∑ i, (coefficient i : ℝ)*x i :=
  FlowBasisCodec.checkBasis_sound edges cell coefficient intercept target checked x hcell

set_option pp.fullNames true
#print axioms addEdge_sound
#print axioms split_sound
#print axioms negative_diagonal_empty
#print axioms affine_flow_bound
end StructuralGoal20261016.DifferenceCell
