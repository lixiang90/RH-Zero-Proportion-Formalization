/- SPDX-License-Identifier: Apache-2.0
First whole-cell actual derivative certificate of the compact Horner oracle.
-/
import StructuralGoal20261016.WindowGridCertificateData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowGridPilot
open WindowGridCertificate WindowGridCertificateData

theorem cell61 : Valid 61 (row 0) := sound (by decide +kernel)

set_option pp.fullNames true
#print axioms cell61
end StructuralGoal20261016.WindowGridPilot
