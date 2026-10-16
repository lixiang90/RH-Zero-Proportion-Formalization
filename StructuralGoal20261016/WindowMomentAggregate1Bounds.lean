/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentAggregateData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowMomentAggregateChecks
open WindowMomentAggregateData WindowMomentPolynomial
theorem check1Bound : (row1.bound:ℚ) = (den1:ℚ)*aggregate1.bound := by decide +kernel
theorem check1Scale : (0:ℤ) < den1 := by decide +kernel
theorem check1Box : ∀ i : Fin 464,
 ((lower1 i:ℚ)/(boxScale:ℚ)) = WindowMomentBox.lower (WindowMomentGlobalBox.global WindowMomentBoxData.box1) i ∧
 ((upper1 i:ℚ)/(boxScale:ℚ)) = WindowMomentBox.upper (WindowMomentGlobalBox.global WindowMomentBoxData.box1) i := by decide +kernel
theorem check1Strict : WindowMomentExactInteger.strictCheck boxScale row1 lower1 upper1 = true := by decide +kernel
set_option pp.fullNames true
#print axioms check1Bound
#print axioms check1Scale
#print axioms check1Box
#print axioms check1Strict
end StructuralGoal20261016.WindowMomentAggregateChecks
