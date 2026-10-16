/- SPDX-License-Identifier: Apache-2.0
Actual value/slope finite checks for anchor indices 0..63.
-/
import StructuralGoal20261016.WindowAnchorCertificateData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowAnchorChecks
open WindowAnchorCertificate WindowAnchorCertificateData
theorem checks00 : ∀ j : Fin 64, 0*64+(j:ℕ) < 1567 →
 check (row (0*64+(j:ℕ))) = true := by decide +kernel
set_option pp.fullNames true
#print axioms checks00
end StructuralGoal20261016.WindowAnchorChecks
