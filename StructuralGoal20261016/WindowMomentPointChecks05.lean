/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentPointData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowMomentPointChecks
open WindowAnchorCertificate WindowMomentPointData
theorem checks05 : ∀ j : Fin 16, 5*16+(j:ℕ) < 82 →
 check (row (5*16+(j:ℕ))) = true := by decide +kernel
set_option pp.fullNames true
#print axioms checks05
end StructuralGoal20261016.WindowMomentPointChecks
