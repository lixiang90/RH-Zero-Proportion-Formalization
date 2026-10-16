/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentAggregateData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowMomentAggregateChecks
open WindowMomentAggregateData WindowMomentPolynomial
theorem check1Gap : ∀ j : Fin 9, ((row1.coeff (WindowMomentLayout.gapIndex j)):ℚ) =
 (den1:ℚ)*flatten aggregate1 (WindowMomentLayout.gapIndex j) := by decide +kernel
set_option pp.fullNames true
#print axioms check1Gap
end StructuralGoal20261016.WindowMomentAggregateChecks
