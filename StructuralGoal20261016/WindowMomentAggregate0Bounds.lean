/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentAggregateData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowMomentAggregateChecks
open WindowMomentAggregateData WindowMomentPolynomial
theorem check0Bound : (row0.bound:ℚ) = (den0:ℚ)*aggregate0.bound := by decide +kernel
theorem check0Scale : (0:ℤ) < den0 := by decide +kernel
theorem check0Box : ∀ i : Fin 464,
 ((lower0 i:ℚ)/(boxScale:ℚ)) = WindowMomentBox.lower (WindowMomentGlobalBox.global WindowMomentBoxData.box0) i ∧
 ((upper0 i:ℚ)/(boxScale:ℚ)) = WindowMomentBox.upper (WindowMomentGlobalBox.global WindowMomentBoxData.box0) i := by decide +kernel
theorem check0Strict : WindowMomentExactInteger.strictCheck boxScale row0 lower0 upper0 = true := by decide +kernel
set_option pp.fullNames true
#print axioms check0Bound
#print axioms check0Scale
#print axioms check0Box
#print axioms check0Strict
end StructuralGoal20261016.WindowMomentAggregateChecks
