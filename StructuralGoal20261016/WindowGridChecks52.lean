/- SPDX-License-Identifier: Apache-2.0
Actual whole-cell derivative checks for separated grid cells
1725..1756.
-/
import StructuralGoal20261016.WindowGridCertificateData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowGridChecks
open WindowGridCertificate WindowGridCertificateData
theorem checks52 : ∀ j : Fin 32, 52*32+(j:ℕ) < 1987 →
 check (61+52*32+(j:ℕ)) (row (52*32+(j:ℕ))) = true := by decide +kernel
set_option pp.fullNames true
#print axioms checks52
end StructuralGoal20261016.WindowGridChecks
