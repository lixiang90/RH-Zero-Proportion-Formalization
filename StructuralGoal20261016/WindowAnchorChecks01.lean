/- SPDX-License-Identifier: Apache-2.0
Actual value/slope finite checks for anchor indices 64..127.
-/
import StructuralGoal20261016.WindowAnchorCertificateData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowAnchorChecks
open WindowAnchorCertificate WindowAnchorCertificateData
theorem checks01 : ∀ j : Fin 64, 1*64+(j:ℕ) < 1567 →
 check (row (1*64+(j:ℕ))) = true := by decide +kernel
set_option pp.fullNames true
#print axioms checks01
end StructuralGoal20261016.WindowAnchorChecks
