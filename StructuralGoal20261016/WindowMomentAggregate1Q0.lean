/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentAggregateData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowMomentAggregateChecks
open WindowMomentAggregateData WindowMomentPolynomial
theorem check1Q0 : ∀ s : Fin 3, ∀ e : Fin 41,
 ((row1.coeff (WindowMomentLayout.qIndex ⟨0*3+(s:ℕ),by omega⟩ e)):ℚ) =
 (den1:ℚ)*flatten aggregate1 (WindowMomentLayout.qIndex ⟨0*3+(s:ℕ),by omega⟩ e) := by
 have hf (s : Fin 3) (e : Fin 41) :
     flatten aggregate1 (WindowMomentLayout.qIndex ⟨0*3+(s:ℕ),by omega⟩ e) =
       aggregate1.q ⟨0*3+(s:ℕ),by omega⟩ e :=
   flatten_encode aggregate1 (.inr (.inr (.inr (⟨0*3+(s:ℕ),by omega⟩,e))))
 simp only [hf]
 simp only [aggregate1,WindowMomentFormSum.add,WindowMomentFormSum.sumForms,
   groups1,grouped,energy1,WindowMomentFormSum.scale,
   WindowMomentEnergyPolynomial.energyForm,WindowMomentEnergyPolynomial.form]
 intro s e
 fin_cases s <;> fin_cases e <;> decide +kernel
set_option pp.fullNames true
#print axioms check1Q0
end StructuralGoal20261016.WindowMomentAggregateChecks
