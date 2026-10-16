/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentPointData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowMomentPointChecks
open WindowAnchorCertificate WindowMomentPointData
theorem checks03 : ∀ j : Fin 16, 3*16+(j:ℕ) < 82 →
 check (row (3*16+(j:ℕ))) = true := by decide +kernel
set_option pp.fullNames true
#print axioms checks03
end StructuralGoal20261016.WindowMomentPointChecks
