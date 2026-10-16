/- SPDX-License-Identifier: Apache-2.0
All 24 actual OBBT facts for the two parents of the local three-leaf tree.
-/
import StructuralGoal20261016.WindowCurvatureOBBT00
import StructuralGoal20261016.WindowCurvatureOBBTGroup00
import StructuralGoal20261016.WindowCurvatureOBBTGroup01
import StructuralGoal20261016.WindowCurvatureOBBTGroup02
set_option Elab.async false
set_option maxHeartbeats 0
namespace StructuralGoal20261016.WindowCurvatureOBBTAll
open WindowCurvatureOBBTDispatch WindowCurvatureOBBTGroups
theorem checked (i : Fin 24) : WindowMixedContractions.obbtCheck WindowMixedCover.target880
 (input i) (bound i) = true := by
 fin_cases i
 · exact WindowCurvatureOBBT.checked00
 · exact checks00 ⟨0,by decide⟩ (by decide)
 · exact checks00 ⟨1,by decide⟩ (by decide)
 · exact checks00 ⟨2,by decide⟩ (by decide)
 · exact checks00 ⟨3,by decide⟩ (by decide)
 · exact checks00 ⟨4,by decide⟩ (by decide)
 · exact checks00 ⟨5,by decide⟩ (by decide)
 · exact checks00 ⟨6,by decide⟩ (by decide)
 · exact checks00 ⟨7,by decide⟩ (by decide)
 · exact checks01 ⟨0,by decide⟩ (by decide)
 · exact checks01 ⟨1,by decide⟩ (by decide)
 · exact checks01 ⟨2,by decide⟩ (by decide)
 · exact checks01 ⟨3,by decide⟩ (by decide)
 · exact checks01 ⟨4,by decide⟩ (by decide)
 · exact checks01 ⟨5,by decide⟩ (by decide)
 · exact checks01 ⟨6,by decide⟩ (by decide)
 · exact checks01 ⟨7,by decide⟩ (by decide)
 · exact checks02 ⟨0,by decide⟩ (by decide)
 · exact checks02 ⟨1,by decide⟩ (by decide)
 · exact checks02 ⟨2,by decide⟩ (by decide)
 · exact checks02 ⟨3,by decide⟩ (by decide)
 · exact checks02 ⟨4,by decide⟩ (by decide)
 · exact checks02 ⟨5,by decide⟩ (by decide)
 · exact checks02 ⟨6,by decide⟩ (by decide)
set_option pp.fullNames true
#print axioms checked
end StructuralGoal20261016.WindowCurvatureOBBTAll
