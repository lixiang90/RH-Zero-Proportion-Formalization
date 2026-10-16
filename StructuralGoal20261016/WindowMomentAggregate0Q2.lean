/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentAggregateData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowMomentAggregateChecks
open WindowMomentAggregateData WindowMomentPolynomial
theorem check0Q2 : ∀ s : Fin 3, ∀ e : Fin 41,
 ((row0.coeff (WindowMomentLayout.qIndex ⟨2*3+(s:ℕ),by omega⟩ e)):ℚ) =
 (den0:ℚ)*flatten aggregate0 (WindowMomentLayout.qIndex ⟨2*3+(s:ℕ),by omega⟩ e) := by
 have hf (s : Fin 3) (e : Fin 41) :
     flatten aggregate0 (WindowMomentLayout.qIndex ⟨2*3+(s:ℕ),by omega⟩ e) =
       aggregate0.q ⟨2*3+(s:ℕ),by omega⟩ e :=
   flatten_encode aggregate0 (.inr (.inr (.inr (⟨2*3+(s:ℕ),by omega⟩,e))))
 simp only [hf]
 simp only [aggregate0,WindowMomentFormSum.add,WindowMomentFormSum.sumForms,
   groups0,grouped,energy0,WindowMomentFormSum.scale,
   WindowMomentEnergyPolynomial.energyForm,WindowMomentEnergyPolynomial.form]
 intro s e
 fin_cases s <;> fin_cases e <;> decide +kernel
set_option pp.fullNames true
#print axioms check0Q2
end StructuralGoal20261016.WindowMomentAggregateChecks
