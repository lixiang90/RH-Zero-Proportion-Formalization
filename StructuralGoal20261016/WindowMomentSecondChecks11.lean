/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentSecondData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowMomentSecondChecks
open WindowCurvatureGrid WindowMomentSecondData
theorem checks11 : ∀ j : Fin 32, 11*32+(j:ℕ) < 403 →
 check (newRow (11*32+(j:ℕ))) = true := by decide +kernel
set_option pp.fullNames true
#print axioms checks11
end StructuralGoal20261016.WindowMomentSecondChecks
