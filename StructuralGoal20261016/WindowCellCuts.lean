/- SPDX-License-Identifier: Apache-2.0
Checked geometric cuts and original-orthant direction feasibility for
the actual difference-cell cover. Every cut in a simultaneous contraction
is certified at the original parent; closure is applied only afterwards.
-/
import StructuralGoal20261016.WindowDifferenceCell
import StructuralGoal20261016.WindowValueSublevel
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators
open Zeta23Ext.Bridge
namespace StructuralGoal20261016.WindowCellCuts
open WindowDifferenceCell (Contains positions)

structure Cut where
  i : Fin 10
  j : Fin 10
  bound : ℤ

def restrict (cell : DifferenceCell.Cell 10) (cuts : List Cut) : DifferenceCell.Cell 10 :=
  cuts.foldl (fun c e => DifferenceCell.addEdge c e.i e.j e.bound) cell

theorem restrict_sound {cell : DifferenceCell.Cell 10} {g : Fin 9 → ℝ}
    (cuts : List Cut) (hg : Contains cell g)
    (hcuts : ∀ e ∈ cuts, positions g e.j-positions g e.i ≤ (e.bound:ℝ)) :
    Contains (restrict cell cuts) g := by
  induction cuts generalizing cell with
  | nil => exact hg
  | cons e es ih =>
    change Contains (restrict (DifferenceCell.addEdge cell e.i e.j e.bound) es) g
    apply ih
    · exact DifferenceCell.addEdge_sound hg e.i e.j e.bound (hcuts e (by simp))
    · intro a ha
      exact hcuts a (by simp [ha])

def negativeIncidence (i j : Fin 10) (r : Fin 9) : ℤ :=
  (if (r:ℕ) < (i:ℕ) then 1 else 0)-(if (r:ℕ) < (j:ℕ) then 1 else 0)

theorem objective_eq (i j : Fin 10) (g : Fin 9 → ℝ) :
    WindowValueSublevel.objective (negativeIncidence i j) g =
      positions g i-positions g j := by
  have hs : (∑ r : Fin 9, (negativeIncidence i j r:ℝ)*g r) = ptsN 10 g i-ptsN 10 g j := by
    unfold negativeIncidence ptsN
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    split_ifs <;> norm_num <;> ring
  unfold WindowValueSublevel.objective positions
  rw [hs]
  ring

theorem adjacent (g : Fin 9 → ℝ) (r : Fin 9) :
    positions g r.succ-positions g r.castSucc = 32768*g r := by
  have h := WindowDifferenceCell.adjacent_difference g r
  unfold positions
  linarith

theorem interior_of_bound {sep : ℚ} {cell : DifferenceCell.Cell 10} {g : Fin 9 → ℝ}
    (hg : Contains cell g) (r : Fin 9)
    (hbound : sep*32768 < -(cell r.succ r.castSucc:ℚ)) : (sep:ℝ) < g r := by
  have hc := hg r.succ r.castSucc
  change positions g r.castSucc-positions g r.succ ≤ (cell r.succ r.castSucc:ℝ) at hc
  have hp : ((sep*32768:ℚ):ℝ) < ((-(cell r.succ r.castSucc:ℚ):ℚ):ℝ) := Rat.cast_lt.mpr hbound
  push_cast at hp
  have ha := adjacent g r
  linarith

def supportCheck (sep : ℚ) (cell : DifferenceCell.Cell 10) (d : Fin 9 → ℤ) : Bool :=
  decide (∀ r : Fin 9, d r ≠ 0 → sep*32768 < -(cell r.succ r.castSucc:ℚ))

theorem support_sound {sep : ℚ} {cell : DifferenceCell.Cell 10} {d : Fin 9 → ℤ}
    (hc : supportCheck sep cell d = true) {g : Fin 9 → ℝ} (hg : Contains cell g) :
    ∀ r, d r ≠ 0 → (sep:ℝ) < g r := by
  have hh : ∀ r : Fin 9, d r ≠ 0 → sep*32768 < -(cell r.succ r.castSucc:ℚ) :=
    of_decide_eq_true hc
  intro r hr
  exact interior_of_bound hg r (hh r hr)

def feasibleCheck (sep : ℚ) (cell : DifferenceCell.Cell 10) (d : Fin 9 → ℤ) : Bool :=
  decide (∀ r : Fin 9, 0 ≤ d r ∨ sep*32768 < -(cell r.succ r.castSucc:ℚ))

theorem feasible_sound {sep : ℚ} {cell : DifferenceCell.Cell 10} {d : Fin 9 → ℤ}
    (hc : feasibleCheck sep cell d = true) {g : Fin 9 → ℝ} (hg : Contains cell g) :
    ∀ r, g r = (sep:ℝ) → 0 ≤ d r := by
  have hh : ∀ r : Fin 9, 0 ≤ d r ∨ sep*32768 < -(cell r.succ r.castSucc:ℚ) :=
    of_decide_eq_true hc
  intro r hr
  rcases hh r with h | h
  · exact h
  · have hi := interior_of_bound hg r h
    exact False.elim (by linarith)

def axisI (a : ℕ) : Fin 10 := ⟨(a/10)%10,by omega⟩
def axisJ (a : ℕ) : Fin 10 := ⟨a%10,by omega⟩

def branchCheck (a : ℕ) : Bool := decide (a < 100 ∧ (axisI a:ℕ) < (axisJ a:ℕ))
def left (cell : DifferenceCell.Cell 10) (a q : ℕ) : DifferenceCell.Cell 10 :=
  DifferenceCell.addEdge cell (axisI a) (axisJ a) (q:ℤ)
def right (cell : DifferenceCell.Cell 10) (a q : ℕ) : DifferenceCell.Cell 10 :=
  DifferenceCell.addEdge cell (axisJ a) (axisI a) (-(q:ℤ))

theorem split_sound {cell : DifferenceCell.Cell 10} {g : Fin 9 → ℝ}
    (hg : Contains cell g) (a q : ℕ) : Contains (left cell a q) g ∨ Contains (right cell a q) g :=
  WindowDifferenceCell.split_sound hg (axisI a) (axisJ a) (q:ℤ)

set_option pp.fullNames true
#print axioms restrict_sound
#print axioms objective_eq
#print axioms support_sound
#print axioms feasible_sound
#print axioms split_sound
end StructuralGoal20261016.WindowCellCuts
end
