/- SPDX-License-Identifier: Apache-2.0
Actual scalar/capacity/rounding/forest-flow OBBT check 0 of 24.
-/
import StructuralGoal20261016.WindowCurvatureSubtreeData
import StructuralGoal20261016.WindowMixedCover
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowCurvatureOBBT
open WindowCurvatureSubtreeData
theorem checked00 : WindowMixedContractions.obbtCheck WindowMixedCover.target880 parent bound00 = true := by
 decide +kernel
set_option pp.fullNames true
#print axioms checked00
end StructuralGoal20261016.WindowCurvatureOBBT
