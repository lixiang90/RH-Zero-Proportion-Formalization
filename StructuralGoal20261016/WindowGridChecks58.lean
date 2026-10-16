/- SPDX-License-Identifier: Apache-2.0
Actual whole-cell derivative checks for separated grid cells
1917..1948.
-/
import StructuralGoal20261016.WindowGridCertificateData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowGridChecks
open WindowGridCertificate WindowGridCertificateData
theorem checks58 : ∀ j : Fin 32, 58*32+(j:ℕ) < 1987 →
 check (61+58*32+(j:ℕ)) (row (58*32+(j:ℕ))) = true := by decide +kernel
set_option pp.fullNames true
#print axioms checks58
end StructuralGoal20261016.WindowGridChecks
