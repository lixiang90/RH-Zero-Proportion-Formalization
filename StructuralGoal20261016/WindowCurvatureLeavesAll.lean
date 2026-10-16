/- SPDX-License-Identifier: Apache-2.0
Three actual negative-second-variation cells, collected for the cover.
Each theorem still requires membership in its specified cell; these local
exclusions alone do not constitute a complete cover or a zero-proportion bound.
-/
import StructuralGoal20261016.WindowCurvatureLeaf00
import StructuralGoal20261016.WindowCurvatureLeaf01
import StructuralGoal20261016.WindowCurvatureLeaf02
set_option Elab.async false
set_option maxHeartbeats 0
namespace StructuralGoal20261016.WindowCurvatureLeavesAll
open WindowCurvatureLeafData WindowCurvatureLeaves
def cell (i : Fin 3) : DifferenceCell.Cell 10 := ![cell00,cell01,cell02] i
theorem exclude (i : Fin 3) {g : Fin 9 → ℝ}
 (hg : WindowMinimizerCover.Relevant ((123:ℝ)/128) g)
 (hcell : WindowDifferenceCell.Contains (cell i) g) : False := by
 fin_cases i
 · exact exclude00 hg hcell
 · exact exclude01 hg hcell
 · exact exclude02 hg hcell
set_option pp.fullNames true
#print axioms exclude
end StructuralGoal20261016.WindowCurvatureLeavesAll
