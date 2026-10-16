/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentAggregateActual
import StructuralGoal20261016.WindowMomentAggregate0Gap
import StructuralGoal20261016.WindowMomentAggregate0Scalar
import StructuralGoal20261016.WindowMomentAggregate0H
import StructuralGoal20261016.WindowMomentAggregate0Q0
import StructuralGoal20261016.WindowMomentAggregate0Q1
import StructuralGoal20261016.WindowMomentAggregate0Q2
import StructuralGoal20261016.WindowMomentAggregate0Bounds
import StructuralGoal20261016.WindowMomentEnergyCase00
import StructuralGoal20261016.WindowMomentBoxCase00
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowMomentExclusions
open WindowMomentAggregateData WindowMomentAggregateChecks WindowMomentPolynomial
open WindowMomentAtomData WindowMomentEnergyData WindowMomentBoxData
theorem radius0 : ∀ r : Fin 9, 0 < box0.radius r := by decide +kernel

theorem qComplete0 (s : Fin 9) (e : Fin 41) :
 (row0.coeff (WindowMomentLayout.qIndex s e):ℚ) =
 (den0:ℚ)*flatten aggregate0 (WindowMomentLayout.qIndex s e) := by
 fin_cases s
 · exact check0Q0 0 e
 · exact check0Q0 1 e
 · exact check0Q0 2 e
 · exact check0Q1 0 e
 · exact check0Q1 1 e
 · exact check0Q1 2 e
 · exact check0Q2 0 e
 · exact check0Q2 1 e
 · exact check0Q2 2 e

theorem exactChecked0 : WindowMomentExactInteger.check den0
 (flatten aggregate0) aggregate0.bound row0 = true := by
 unfold WindowMomentExactInteger.check
 rw [decide_eq_true_eq]
 refine ⟨check0Scale,?_,check0Bound⟩
 intro i
 rw [← WindowMomentPolynomial.encode_decode i]
 generalize WindowMomentPolynomial.decode i = b
 cases b with
 | inl r => exact check0Gap r
 | inr b =>
   cases b with
   | inl e => exact check0Scalar e
   | inr b =>
     cases b with
     | inl e => exact check0H e
     | inr p => exact qComplete0 p.1 p.2

theorem actualBound0 {g : Fin 9 → ℝ}
 (hg : WindowMinimizerCover.Relevant ((123/128:ℚ):ℝ) g)
 (hcell : WindowDifferenceCell.Contains cell0 g)
 (hbelow : WindowGapEnergy.Fw24 g < ((11/1250:ℚ):ℝ)) :
 eval aggregate0 (realVector box0.center) (realVector box0.radius) g ≤
 (aggregate0.bound:ℝ) :=
 WindowMomentAggregateActual.actualBound0 hg hcell hbelow

theorem exclude0 {g : Fin 9 → ℝ}
 (hg : WindowMinimizerCover.Relevant ((123/128:ℚ):ℝ) g)
 (hcell : WindowDifferenceCell.Contains cell0 g)
 (hbelow : WindowGapEnergy.Fw24 g < ((11/1250:ℚ):ℝ)) : False := by
 have hgeometry : WindowMomentBox.checkGeometry cell0 box0 = true := by decide +kernel
 have hb := WindowMomentGlobalBox.sound hgeometry hcell
 have hx : ∀ i, (lower0 i:ℝ)/(boxScale:ℝ) ≤ WindowMomentBox.actual box0 g i ∧
     WindowMomentBox.actual box0 g i ≤ (upper0 i:ℝ)/(boxScale:ℝ) := by
   intro i
   have hl : (((lower0 i:ℚ)/(boxScale:ℚ):ℚ):ℝ) =
       ((WindowMomentBox.lower (WindowMomentGlobalBox.global box0) i):ℝ) :=
     congrArg (fun x : ℚ => (x:ℝ)) (check0Box i).1
   have hu : (((upper0 i:ℚ)/(boxScale:ℚ):ℚ):ℝ) =
       ((WindowMomentBox.upper (WindowMomentGlobalBox.global box0) i):ℝ) :=
     congrArg (fun x : ℚ => (x:ℝ)) (check0Box i).2
   push_cast at hl hu
   rw [hl,hu]
   exact hb i
 exact WindowMomentExactInteger.exclude lower0 upper0 exactChecked0 check0Strict
   (WindowMomentBox.actual box0 g) hx (actualBound0 hg hcell hbelow)
set_option pp.fullNames true
#print axioms exactChecked0
#print axioms actualBound0
#print axioms exclude0
end StructuralGoal20261016.WindowMomentExclusions
end
