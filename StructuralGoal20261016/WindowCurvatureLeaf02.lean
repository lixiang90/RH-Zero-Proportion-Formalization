/- SPDX-License-Identifier: Apache-2.0
Actual second-variation exclusion on frozen cell r0010000011011011100011101.
This is local to that cell and does not assert completion of a global cover.
-/
import StructuralGoal20261016.WindowCurvatureLeafData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowCurvatureLeaves
open WindowCurvatureLeafData
theorem scalar02 : WindowCurvatureScalar.allCheck cell02 rows02 packets02 = true := by
 decide +kernel
theorem support02 : WindowCurvatureScalar.supportCheck cell02 direction02 = true := by
 decide +kernel
theorem flow02 : WindowCurvatureFlow.check cell02 edges02 direction02 rows02 = true := by
 decide +kernel
theorem exclude02 {g : Fin 9 → ℝ}
 (hg : WindowMinimizerCover.Relevant ((123:ℝ)/128) g)
 (hcell : WindowDifferenceCell.Contains cell02 g) : False :=
 WindowCurvatureScalar.exclude scalar02 support02 flow02 hg hcell
set_option pp.fullNames true
#print axioms scalar02
#print axioms support02
#print axioms flow02
#print axioms exclude02
end StructuralGoal20261016.WindowCurvatureLeaves
