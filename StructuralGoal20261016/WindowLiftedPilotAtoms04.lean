/- SPDX-License-Identifier: Apache-2.0
Actual lifted atom checks 32..39.
-/
import StructuralGoal20261016.WindowLiftedPilotData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowLiftedPilotAtoms
open WindowLiftedPilotData
theorem checks04 : ∀ k : Fin 8, 4*8+(k:ℕ) < 43 →
 WindowLiftedKKT.checkAtom (123/128) cell (atom (4*8+(k:ℕ))) = true := by decide +kernel
set_option pp.fullNames true
#print axioms checks04
end StructuralGoal20261016.WindowLiftedPilotAtoms
