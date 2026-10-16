/- SPDX-License-Identifier: Apache-2.0
Actual energy-packet consumer. Checked fixed-point values/slopes and checked
whole-cell second derivative bounds feed the signed Taylor lower polynomial.
All geometric and table-lookup obligations are explicit rational checks.
-/
import StructuralGoal20261016.WindowMomentEnergy
import StructuralGoal20261016.WindowMomentPointAll
import StructuralGoal20261016.WindowMomentSecondAll
import StructuralGoal20261016.WindowFirstOrderCertificate
import StructuralGoal20261016.WindowCellCuts
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set
open scoped BigOperators
namespace StructuralGoal20261016.WindowMomentEnergyCertificate
open WindowGramTransfer

structure Packet where
 center : Fin 9 → ℚ
 radius : Fin 9 → ℚ
 point : Fin 41 → ℕ
 firstCell : Fin 41 → ℕ
 lastCell : Fin 41 → ℕ
 secondLower : Fin 41 → ℚ
 secondUpper : Fin 41 → ℚ

def spanQ (p : Fin 9 → ℚ) (e : Fin 41) : ℚ :=
 ∑ r, p r*(WindowDirectionalFlow.incidence e r:ℚ)

theorem span_cast (p : Fin 9 → ℚ) (e : Fin 41) :
 (spanQ p e:ℝ) = span (fun r => (p r:ℝ)) e := by
 unfold spanQ
 push_cast
 rw [WindowDirectionalAffine.span_eq_sum]
 apply Finset.sum_congr rfl
 intro r _
 rw [WindowDirectionalFlow.incidence_cast]

def pointRow (p : Packet) (e : Fin 41) : WindowAnchorCertificate.Row :=
 WindowMomentPointData.row (p.point e)
def V (p : Packet) (e : Fin 41) : ℝ := ((pointRow p e).lower:ℝ)
def S (p : Packet) (e : Fin 41) : ℝ := ((pointRow p e).slope:ℝ)
def E (p : Packet) (e : Fin 41) : ℝ := ((pointRow p e).error:ℝ)
def leftQ (cell : DifferenceCell.Cell 10) (e : Fin 41) : ℚ :=
 WindowFirstOrderCertificate.leftQ cell e
def rightQ (cell : DifferenceCell.Cell 10) (e : Fin 41) : ℚ :=
 WindowFirstOrderCertificate.rightQ cell e

def checkGeometry (cell : DifferenceCell.Cell 10) (p : Packet) : Bool := decide (
 (∀ r, p.center r-p.radius r ≤ -(cell r.succ r.castSucc:ℚ)/32768 ∧
   (cell r.castSucc r.succ:ℚ)/32768 ≤ p.center r+p.radius r) ∧
 (∀ e, p.point e < 82 ∧ (pointRow p e).anchor = spanQ p.center e ∧
   leftQ cell e ≤ spanQ p.center e ∧ spanQ p.center e ≤ rightQ cell e))

def checkSecond (cell : DifferenceCell.Cell 10) (p : Packet) : Bool := decide (
 ∀ e, WindowCurvatureGrid.secondCheck WindowMomentSecondData.row
   WindowMomentSecondData.index 734 (p.firstCell e) (p.lastCell e)
   (leftQ cell e) (rightQ cell e) (p.secondLower e) (p.secondUpper e) = true)

def check (cell : DifferenceCell.Cell 10) (p : Packet) : Bool :=
 checkGeometry cell p && checkSecond cell p

def polynomial (p : Packet) (g : Fin 9 → ℝ) : ℝ :=
 WindowMomentEnergy.polynomial (fun r => (p.center r:ℝ)) g (V p) (S p)
   (fun e => (p.secondLower e:ℝ)) (E p) (fun r => (p.radius r:ℝ))

theorem lower {cell : DifferenceCell.Cell 10} {p : Packet}
 (hc : check cell p = true) {g : Fin 9 → ℝ}
 (hg : WindowDifferenceCell.Contains cell g) :
 polynomial p g ≤ WindowGapEnergy.Fw24 g := by
 have hh : checkGeometry cell p = true ∧ checkSecond cell p = true := by
   simpa only [check,Bool.and_eq_true] using hc
 have hgeom : (∀ r, p.center r-p.radius r ≤ -(cell r.succ r.castSucc:ℚ)/32768 ∧
     (cell r.castSucc r.succ:ℚ)/32768 ≤ p.center r+p.radius r) ∧
     (∀ e, p.point e < 82 ∧ (pointRow p e).anchor = spanQ p.center e ∧
       leftQ cell e ≤ spanQ p.center e ∧ spanQ p.center e ≤ rightQ cell e) :=
   of_decide_eq_true hh.1
 have hsec : ∀ e, WindowCurvatureGrid.secondCheck WindowMomentSecondData.row
     WindowMomentSecondData.index 734 (p.firstCell e) (p.lastCell e)
     (leftQ cell e) (rightQ cell e) (p.secondLower e) (p.secondUpper e) = true :=
   of_decide_eq_true hh.2
 have hR : ∀ r, |g r-(p.center r:ℝ)| ≤ (p.radius r:ℝ) := by
   intro r
   have hl := hg r.succ r.castSucc
   have hu := hg r.castSucc r.succ
   have ha := WindowCellCuts.adjacent g r
   have hgl : ((p.center r-p.radius r:ℚ):ℝ) ≤ ((-(cell r.succ r.castSucc:ℚ)/32768:ℚ):ℝ) :=
     Rat.cast_le.mpr (hgeom.1 r).1
   have hgu : (((cell r.castSucc r.succ:ℚ)/32768:ℚ):ℝ) ≤ ((p.center r+p.radius r:ℚ):ℝ) :=
     Rat.cast_le.mpr (hgeom.1 r).2
   push_cast at hgl hgu
   apply abs_le.mpr
   change WindowDifferenceCell.positions g r.castSucc-
     WindowDifferenceCell.positions g r.succ ≤ (cell r.succ r.castSucc:ℝ) at hl
   change WindowDifferenceCell.positions g r.succ-
     WindowDifferenceCell.positions g r.castSucc ≤ (cell r.castSucc r.succ:ℝ) at hu
   constructor <;> linarith
 have hp : ∀ e, span (fun r => (p.center r:ℝ)) e ∈
     Icc (leftQ cell e:ℝ) (rightQ cell e:ℝ) := by
   intro e
   rw [← span_cast]
   exact ⟨Rat.cast_le.mpr (hgeom.2 e).2.2.1,Rat.cast_le.mpr (hgeom.2 e).2.2.2⟩
 have hx : ∀ e, span g e ∈ Icc (leftQ cell e:ℝ) (rightQ cell e:ℝ) := by
   intro e
   have hb := WindowScalarLine.span_bounds hg e
   simpa only [Set.mem_Icc,leftQ,rightQ,WindowFirstOrderCertificate.leftQ,
     WindowFirstOrderCertificate.rightQ,Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat] using hb
 have hpoint : ∀ e, V p e ≤ WindowScalarMinorant.f (span (fun r => (p.center r:ℝ)) e) ∧
     |iteratedDeriv 1 WindowScalarMinorant.f (span (fun r => (p.center r:ℝ)) e)-S p e| ≤ E p e := by
   intro e
   have hv := WindowMomentPointAll.valid (p.point e) (hgeom.2 e).1
   change (V p e ≤ WindowScalarMinorant.f ((pointRow p e).anchor:ℝ)) ∧
     |iteratedDeriv 1 WindowScalarMinorant.f ((pointRow p e).anchor:ℝ)-S p e| ≤ E p e at hv
   rw [(hgeom.2 e).2.1,span_cast] at hv
   exact hv
 exact WindowMomentEnergy.lower _ _ _ _ _ _ _ _ _ hp hx hR
   (fun e => (hpoint e).1) (fun e => (hpoint e).2)
   (fun e x hxe => (WindowMomentSecondAll.second (hsec e) hxe).1)

theorem sublevel {cell : DifferenceCell.Cell 10} {p : Packet} {c : ℝ}
 (hc : check cell p = true) {g : Fin 9 → ℝ}
 (hg : WindowDifferenceCell.Contains cell g) (hbelow : WindowGapEnergy.Fw24 g < c) :
 polynomial p g < c := (lower hc hg).trans_lt hbelow

set_option pp.fullNames true
#print axioms span_cast
#print axioms lower
#print axioms sublevel
end StructuralGoal20261016.WindowMomentEnergyCertificate
end
