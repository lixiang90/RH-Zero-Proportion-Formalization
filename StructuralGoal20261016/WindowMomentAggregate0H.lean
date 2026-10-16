/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentAggregateData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowMomentAggregateChecks
open WindowMomentAggregateData WindowMomentPolynomial
theorem check0H : ∀ j : Fin 45, ((row0.coeff (WindowMomentLayout.hIndex j)):ℚ) =
 (den0:ℚ)*flatten aggregate0 (WindowMomentLayout.hIndex j) := by 
 have hf (j : Fin 45) : flatten aggregate0 (WindowMomentLayout.hIndex j) = aggregate0.h j :=
   flatten_encode aggregate0 (.inr (.inr (.inl j)))
 simp only [hf]
 simp only [aggregate0,WindowMomentFormSum.add,WindowMomentFormSum.sumForms,
   groups0,grouped,energy0,WindowMomentFormSum.scale,
   WindowMomentEnergyPolynomial.energyForm,WindowMomentEnergyPolynomial.form,
   collectH,Fintype.sum_prod_type]
 intro j
 fin_cases j <;> decide +kernel
set_option pp.fullNames true
#print axioms check0H
end StructuralGoal20261016.WindowMomentAggregateChecks
