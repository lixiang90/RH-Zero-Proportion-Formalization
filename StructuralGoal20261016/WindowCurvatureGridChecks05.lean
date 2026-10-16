/- SPDX-License-Identifier: Apache-2.0
Actual selected derivative cell checks, indices 160..191.
-/
import StructuralGoal20261016.WindowCurvatureGridData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowCurvatureGridChecks
open WindowCurvatureGrid WindowCurvatureGridData
theorem checks05 : ∀ j : Fin 32, 5*32+(j:ℕ) < 331 →
 check (row (5*32+(j:ℕ))) = true := by decide +kernel
set_option pp.fullNames true
#print axioms checks05
end StructuralGoal20261016.WindowCurvatureGridChecks
