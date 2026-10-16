/- SPDX-License-Identifier: Apache-2.0
Actual selected derivative cell checks, indices 128..159.
-/
import StructuralGoal20261016.WindowCurvatureGridData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowCurvatureGridChecks
open WindowCurvatureGrid WindowCurvatureGridData
theorem checks04 : ∀ j : Fin 32, 4*32+(j:ℕ) < 331 →
 check (row (4*32+(j:ℕ))) = true := by decide +kernel
set_option pp.fullNames true
#print axioms checks04
end StructuralGoal20261016.WindowCurvatureGridChecks
