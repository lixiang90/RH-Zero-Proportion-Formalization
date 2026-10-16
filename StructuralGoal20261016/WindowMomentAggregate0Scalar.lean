/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentAggregateData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowMomentAggregateChecks
open WindowMomentAggregateData WindowMomentPolynomial
theorem check0Scalar : ∀ j : Fin 41, ((row0.coeff (WindowMomentLayout.uIndex j)):ℚ) =
 (den0:ℚ)*flatten aggregate0 (WindowMomentLayout.uIndex j) := by decide +kernel
set_option pp.fullNames true
#print axioms check0Scalar
end StructuralGoal20261016.WindowMomentAggregateChecks
