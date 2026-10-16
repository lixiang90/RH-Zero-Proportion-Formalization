/- SPDX-License-Identifier: Apache-2.0
Small edge-only flow witnesses. Reconstruction is untrusted computation;
the checker independently verifies nonnegativity, balance, and exact cost.
Consequently decoder correctness and LP optimality are not proof premises.
-/
import StructuralGoal20261016.AffineFlowCertificate
set_option Elab.async false
set_option maxHeartbeats 0
namespace StructuralGoal20261016.FlowBasisCodec

abbrev Edge := ℕ × ℕ
abbrev AmountEdge := ℕ × ℕ × ℤ

def incident (u : ℕ) (edge : Edge) : Bool := edge.1 == u || edge.2 == u

def reconstructAux (n : ℕ) : ℕ → List Edge → List ℤ → List AmountEdge
  | 0, _, _ => []
  | fuel+1, edges, div =>
    match (List.range n).find? (fun u => (edges.filter (incident u)).length == 1) with
    | none => []
    | some u =>
      match edges.find? (incident u) with
      | none => []
      | some edge =>
        let v := if edge.1 == u then edge.2 else edge.1
        let du := div[u]?.getD 0
        let amount := if edge.1 == u then du else -du
        let next := div.mapIdx (fun k value =>
          if k == u then 0 else if k == v then value + du else value)
        (edge.1, edge.2, amount) :: reconstructAux n fuel (edges.erase edge) next

def reconstructed {n : ℕ} (edges : List Edge) (coefficient : Fin n → ℤ) :
    List AmountEdge := reconstructAux n edges.length edges (List.ofFn coefficient)

def matrixOf (edges : List AmountEdge) {n : ℕ} (i j : Fin n) : ℤ :=
  edges.foldl (fun acc edge => acc +
    if edge.1 == i.val && edge.2.1 == j.val then edge.2.2 else 0) 0

def checkFlow {n : ℕ} (flow upper : Fin n → Fin n → ℤ)
    (coefficient : Fin n → ℤ) (intercept target : ℤ) : Bool :=
  decide (∀ i j, 0 ≤ flow i j) &&
    (decide (∀ i, (∑ j, flow i j) - (∑ j, flow j i) = coefficient i) &&
      decide (target ≤ intercept - ∑ i, ∑ j, flow i j * upper i j))

def checkBasis {n : ℕ} (edges : List Edge) (upper : Fin n → Fin n → ℤ)
    (coefficient : Fin n → ℤ) (intercept target : ℤ) : Bool :=
  checkFlow (matrixOf (reconstructed edges coefficient)) upper coefficient intercept target

noncomputable section
open Finset

theorem checkFlow_sound {n : ℕ} (flow upper : Fin n → Fin n → ℤ)
    (coefficient : Fin n → ℤ) (intercept target : ℤ)
    (checked : checkFlow flow upper coefficient intercept target = true)
    (x : Fin n → ℝ)
    (hedge : ∀ i j, x j - x i ≤ (upper i j : ℝ)) :
    (target : ℝ) ≤ (intercept : ℝ) + ∑ i, (coefficient i : ℝ) * x i := by
  simp only [checkFlow, Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨hpos, hbal, hcost⟩ := checked
  have hposR : ∀ i j, (0 : ℝ) ≤ (flow i j : ℝ) := by
    intro i j
    exact_mod_cast hpos i j
  have hbalR : ∀ i, (∑ j, (flow i j : ℝ)) - (∑ j, (flow j i : ℝ)) =
      (coefficient i : ℝ) := by
    intro i
    exact_mod_cast hbal i
  have hlo := AffineFlowCertificate.flow_lower_bound
    (fun i j => (flow i j : ℝ)) (fun i j => (upper i j : ℝ))
    x (fun i => (coefficient i : ℝ)) hposR hedge hbalR
  have hcostR : (target : ℝ) ≤ (intercept : ℝ) -
      ∑ i, ∑ j, (flow i j : ℝ) * (upper i j : ℝ) := by
    exact_mod_cast hcost
  linarith

theorem checkBasis_sound {n : ℕ} (edges : List Edge) (upper : Fin n → Fin n → ℤ)
    (coefficient : Fin n → ℤ) (intercept target : ℤ)
    (checked : checkBasis edges upper coefficient intercept target = true)
    (x : Fin n → ℝ)
    (hedge : ∀ i j, x j - x i ≤ (upper i j : ℝ)) :
    (target : ℝ) ≤ (intercept : ℝ) + ∑ i, (coefficient i : ℝ) * x i :=
  checkFlow_sound _ upper coefficient intercept target checked x hedge

set_option pp.fullNames true
#print axioms checkFlow_sound
#print axioms checkBasis_sound
end
end StructuralGoal20261016.FlowBasisCodec
