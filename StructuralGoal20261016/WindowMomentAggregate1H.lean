/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentAggregateData
import StructuralGoal20261016.WindowMomentCollectHDirect
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowMomentAggregateChecks
open WindowMomentAggregateData WindowMomentPolynomial
theorem check1H : ∀ j : Fin 45, ((row1.coeff (WindowMomentLayout.hIndex j)):ℚ) =
 (den1:ℚ)*flatten aggregate1 (WindowMomentLayout.hIndex j) := by 
 have hf (j : Fin 45) : flatten aggregate1 (WindowMomentLayout.hIndex j) = aggregate1.h j :=
   flatten_encode aggregate1 (.inr (.inr (.inl j)))
 simp only [hf]
 simp only [aggregate1,WindowMomentFormSum.add,WindowMomentFormSum.sumForms,
   groups1,grouped,energy1,WindowMomentFormSum.scale,
   WindowMomentEnergyPolynomial.energyForm,WindowMomentEnergyPolynomial.form,
   WindowMomentCollectHDirect.direct]
 intro j
 fin_cases j <;> decide +kernel
set_option pp.fullNames true
#print axioms check1H
end StructuralGoal20261016.WindowMomentAggregateChecks
