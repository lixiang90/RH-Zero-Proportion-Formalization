/- SPDX-License-Identifier: Apache-2.0
Global ±7 boxes for derivative and mixed coordinates need no local grid
queries. Gap geometry and the actual normalized products supply all bounds.
-/
import StructuralGoal20261016.WindowMomentBox
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
namespace StructuralGoal20261016.WindowMomentGlobalBox
open WindowMomentBox

def global (p : Packet) : Packet := {p with uLower := fun _ => -7, uUpper := fun _ => 7}

theorem sound {cell : DifferenceCell.Cell 10} {p : Packet}
 (hc : checkGeometry cell p = true) {g : Fin 9 → ℝ}
 (hcell : WindowDifferenceCell.Contains cell g) :
 ∀ i, (lower (global p) i:ℝ) ≤ actual p g i ∧ actual p g i ≤ (upper (global p) i:ℝ) := by
 have hgeom : ∀ r, 0 < p.radius r ∧
     p.center r-p.radius r = -(cell r.succ r.castSucc:ℚ)/32768 ∧
     p.center r+p.radius r = (cell r.castSucc r.succ:ℚ)/32768 := of_decide_eq_true hc
 have hr : ∀ r, (0:ℝ) < (p.radius r:ℝ) := fun r => Rat.cast_pos.mpr (hgeom r).1
 have hg : ∀ r, (p.center r:ℝ)-(p.radius r:ℝ) ≤ g r ∧
     g r ≤ (p.center r:ℝ)+(p.radius r:ℝ) := by
   intro r
   have hl := hcell r.succ r.castSucc
   have hu := hcell r.castSucc r.succ
   have ha := WindowCellCuts.adjacent g r
   have hel : ((p.center r-p.radius r:ℚ):ℝ) = ((-(cell r.succ r.castSucc:ℚ)/32768:ℚ):ℝ) :=
     congrArg (fun x : ℚ => (x:ℝ)) (hgeom r).2.1
   have heu : ((p.center r+p.radius r:ℚ):ℝ) = (((cell r.castSucc r.succ:ℚ)/32768:ℚ):ℝ) :=
     congrArg (fun x : ℚ => (x:ℝ)) (hgeom r).2.2
   push_cast at hel heu
   change WindowDifferenceCell.positions g r.castSucc-
     WindowDifferenceCell.positions g r.succ ≤ (cell r.succ r.castSucc:ℝ) at hl
   change WindowDifferenceCell.positions g r.succ-
     WindowDifferenceCell.positions g r.castSucc ≤ (cell r.castSucc r.succ:ℝ) at hu
   constructor <;> linarith
 have hu : ∀ e, (((global p).uLower e):ℝ) ≤ WindowMomentLayout.u g e ∧
     WindowMomentLayout.u g e ≤ (((global p).uUpper e):ℝ) := by
   intro e
   have hb := abs_le.mp (WindowGridRange.fallback (WindowGramTransfer.span g e)).1
   simpa only [global,WindowMomentLayout.u,Rat.cast_neg,Rat.cast_ofNat] using hb
 exact WindowMomentBox.bounds (global p) g hr hg hu

set_option pp.fullNames true
#print axioms sound
end StructuralGoal20261016.WindowMomentGlobalBox
end
