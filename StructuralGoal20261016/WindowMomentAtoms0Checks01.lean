/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentAtomData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowMomentAtomChecks
open WindowMomentAtomData WindowMomentEnergyData
theorem checks0_01 : ∀ j : Fin 16, 1*16+(j:ℕ) < 103 →
 WindowLiftedKKT.checkAtom (123/128) cell0 (atom0 (1*16+(j:ℕ))) = true := by decide +kernel
set_option pp.fullNames true
#print axioms checks0_01
end StructuralGoal20261016.WindowMomentAtomChecks
