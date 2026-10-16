/- SPDX-License-Identifier: Apache-2.0
A coverage checker that preserves only relevant global minimizers.

A contraction is NOT required to preserve all points of its parent cell.
Its soundness obligation preserves the explicitly supplied relevance
predicate. For the zeta application this predicate must include both
global minimality on the full separated orthant and the chosen reflection
orientation. The actual existence/root lemmas are separate theorems.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
set_option Elab.async false
set_option maxHeartbeats 0

namespace StructuralGoal20261016.MinimizerCover

universe u v

structure Operations (Cell : Type u) (Point : Type v) where
  contains : Cell → Point → Prop
  leafCheck : Cell → ℕ → Bool
  branchCheck : Cell → ℕ → ℕ → Bool
  left : Cell → ℕ → ℕ → Cell
  right : Cell → ℕ → ℕ → Cell
  contractionCheck : Cell → ℕ → Bool
  contract : Cell → ℕ → Cell

inductive Tree where
  | leaf (certificate : ℕ)
  | split (axis cut : ℕ) (left right : Tree)
  | contract (certificate : ℕ) (child : Tree)
  deriving Repr

def Tree.check {Cell : Type u} {Point : Type v}
    (ops : Operations Cell Point) : Tree → Cell → Bool
  | .leaf certificate, cell => ops.leafCheck cell certificate
  | .split axis cut left right, cell =>
      ops.branchCheck cell axis cut &&
        (left.check ops (ops.left cell axis cut) &&
          right.check ops (ops.right cell axis cut))
  | .contract certificate child, cell =>
      ops.contractionCheck cell certificate &&
        child.check ops (ops.contract cell certificate)

structure Sound {Cell : Type u} {Point : Type v}
    (ops : Operations Cell Point) (relevant : Point → Prop)
    (F : Point → ℝ) (floor : ℝ) : Prop where
  leaf : ∀ cell certificate x, ops.leafCheck cell certificate = true →
    relevant x → ops.contains cell x → floor ≤ F x
  split : ∀ cell axis cut x, ops.branchCheck cell axis cut = true →
    relevant x → ops.contains cell x →
      ops.contains (ops.left cell axis cut) x ∨
        ops.contains (ops.right cell axis cut) x
  contract : ∀ cell certificate x,
    ops.contractionCheck cell certificate = true →
    relevant x → ops.contains cell x →
      ops.contains (ops.contract cell certificate) x

theorem Tree.check_sound {Cell : Type u} {Point : Type v}
    {ops : Operations Cell Point} {relevant : Point → Prop}
    {F : Point → ℝ} {floor : ℝ} (sound : Sound ops relevant F floor)
    (tree : Tree) (cell : Cell) (checked : tree.check ops cell = true)
    (x : Point) (hx : relevant x) (hcell : ops.contains cell x) :
    floor ≤ F x := by
  induction tree generalizing cell with
  | leaf certificate =>
      exact sound.leaf cell certificate x checked hx hcell
  | split axis cut left right ihl ihr =>
      simp only [Tree.check, Bool.and_eq_true] at checked
      obtain ⟨hb, hl, hr⟩ := checked
      rcases sound.split cell axis cut x hb hx hcell with h | h
      · exact ihl _ hl h
      · exact ihr _ hr h
  | contract certificate child ih =>
      simp only [Tree.check, Bool.and_eq_true] at checked
      obtain ⟨hc, ht⟩ := checked
      exact ih _ ht (sound.contract cell certificate x hc hx hcell)

/-- A checked minimizer cover gives a global floor once a genuine relevant
minimum and the sublevel pressure root have been supplied. The witness is
not inferred from a numerical search or from the existence of a tree. -/
theorem global_floor {Cell : Type u} {Point : Type v}
    {ops : Operations Cell Point} {relevant : Point → Prop}
    {F : Point → ℝ} {floor : ℝ} {domain : Set Point}
    (sound : Sound ops relevant F floor) (tree : Tree) (root : Cell)
    (checked : tree.check ops root = true)
    (minimum : ∃ m, relevant m ∧ ∀ x ∈ domain, F m ≤ F x)
    (root_sublevel : ∀ m, relevant m → F m < floor → ops.contains root m)
    (x : Point) (hx : x ∈ domain) : floor ≤ F x := by
  by_contra h
  have hxf : F x < floor := lt_of_not_ge h
  obtain ⟨m, hm, hmin⟩ := minimum
  have hmf : F m < floor := lt_of_le_of_lt (hmin x hx) hxf
  have hroot := root_sublevel m hm hmf
  have hfloor := tree.check_sound sound root checked m hm hroot
  exact (not_lt_of_ge hfloor) hmf

#print axioms Tree.check_sound
#print axioms global_floor

end StructuralGoal20261016.MinimizerCover
