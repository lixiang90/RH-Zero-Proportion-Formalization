/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentAggregateActual
import StructuralGoal20261016.WindowMomentAggregate1Gap
import StructuralGoal20261016.WindowMomentAggregate1Scalar
import StructuralGoal20261016.WindowMomentAggregate1H
import StructuralGoal20261016.WindowMomentAggregate1Q0
import StructuralGoal20261016.WindowMomentAggregate1Q1
import StructuralGoal20261016.WindowMomentAggregate1Q2
import StructuralGoal20261016.WindowMomentAggregate1Bounds
import StructuralGoal20261016.WindowMomentEnergyCase01
import StructuralGoal20261016.WindowMomentBoxCase01
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowMomentExclusions
open WindowMomentAggregateData WindowMomentAggregateChecks WindowMomentPolynomial
open WindowMomentAtomData WindowMomentEnergyData WindowMomentBoxData
theorem radius1 : ∀ r : Fin 9, 0 < box1.radius r := by decide +kernel

theorem qComplete1 (s : Fin 9) (e : Fin 41) :
 (row1.coeff (WindowMomentLayout.qIndex s e):ℚ) =
 (den1:ℚ)*flatten aggregate1 (WindowMomentLayout.qIndex s e) := by
 fin_cases s
 · exact check1Q0 0 e
 · exact check1Q0 1 e
 · exact check1Q0 2 e
 · exact check1Q1 0 e
 · exact check1Q1 1 e
 · exact check1Q1 2 e
 · exact check1Q2 0 e
 · exact check1Q2 1 e
 · exact check1Q2 2 e

theorem exactChecked1 : WindowMomentExactInteger.check den1
 (flatten aggregate1) aggregate1.bound row1 = true := by
 unfold WindowMomentExactInteger.check
 rw [decide_eq_true_eq]
 refine ⟨check1Scale,?_,check1Bound⟩
 intro i
 rw [← WindowMomentPolynomial.encode_decode i]
 generalize WindowMomentPolynomial.decode i = b
 cases b with
 | inl r => exact check1Gap r
 | inr b =>
   cases b with
   | inl e => exact check1Scalar e
   | inr b =>
     cases b with
     | inl e => exact check1H e
     | inr p => exact qComplete1 p.1 p.2

theorem actualBound1 {g : Fin 9 → ℝ}
 (hg : WindowMinimizerCover.Relevant ((123/128:ℚ):ℝ) g)
 (hcell : WindowDifferenceCell.Contains cell1 g)
 (hbelow : WindowGapEnergy.Fw24 g < ((11/1250:ℚ):ℝ)) :
 eval aggregate1 (realVector box1.center) (realVector box1.radius) g ≤
 (aggregate1.bound:ℝ) :=
 WindowMomentAggregateActual.actualBound1 hg hcell hbelow

theorem exclude1 {g : Fin 9 → ℝ}
 (hg : WindowMinimizerCover.Relevant ((123/128:ℚ):ℝ) g)
 (hcell : WindowDifferenceCell.Contains cell1 g)
 (hbelow : WindowGapEnergy.Fw24 g < ((11/1250:ℚ):ℝ)) : False := by
 have hgeometry : WindowMomentBox.checkGeometry cell1 box1 = true := by decide +kernel
 have hb := WindowMomentGlobalBox.sound hgeometry hcell
 have hx : ∀ i, (lower1 i:ℝ)/(boxScale:ℝ) ≤ WindowMomentBox.actual box1 g i ∧
     WindowMomentBox.actual box1 g i ≤ (upper1 i:ℝ)/(boxScale:ℝ) := by
   intro i
   have hl : (((lower1 i:ℚ)/(boxScale:ℚ):ℚ):ℝ) =
       ((WindowMomentBox.lower (WindowMomentGlobalBox.global box1) i):ℝ) :=
     congrArg (fun x : ℚ => (x:ℝ)) (check1Box i).1
   have hu : (((upper1 i:ℚ)/(boxScale:ℚ):ℚ):ℝ) =
       ((WindowMomentBox.upper (WindowMomentGlobalBox.global box1) i):ℝ) :=
     congrArg (fun x : ℚ => (x:ℝ)) (check1Box i).2
   push_cast at hl hu
   rw [hl,hu]
   exact hb i
 exact WindowMomentExactInteger.exclude lower1 upper1 exactChecked1 check1Strict
   (WindowMomentBox.actual box1 g) hx (actualBound1 hg hcell hbelow)
set_option pp.fullNames true
#print axioms exactChecked1
#print axioms actualBound1
#print axioms exclude1
end StructuralGoal20261016.WindowMomentExclusions
end
