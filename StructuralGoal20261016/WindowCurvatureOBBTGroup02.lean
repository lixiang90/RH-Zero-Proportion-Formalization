/- SPDX-License-Identifier: Apache-2.0
Actual local OBBT checks 17..23.
-/
import StructuralGoal20261016.WindowCurvatureOBBTDispatch
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowCurvatureOBBTGroups
open WindowCurvatureOBBTDispatch
theorem checks02 : ∀ j : Fin 8, 1+2*8+(j:ℕ) < 24 →
 WindowMixedContractions.obbtCheck WindowMixedCover.target880
   (input (1+2*8+(j:ℕ))) (bound (1+2*8+(j:ℕ))) = true := by decide +kernel
set_option pp.fullNames true
#print axioms checks02
end StructuralGoal20261016.WindowCurvatureOBBTGroups
