/- SPDX-License-Identifier: Apache-2.0
Actual second-variation exclusion on frozen cell r001000001101101110001111.
This is local to that cell and does not assert completion of a global cover.
-/
import StructuralGoal20261016.WindowCurvatureLeafData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowCurvatureLeaves
open WindowCurvatureLeafData
theorem scalar01 : WindowCurvatureScalar.allCheck cell01 rows01 packets01 = true := by
 decide +kernel
theorem support01 : WindowCurvatureScalar.supportCheck cell01 direction01 = true := by
 decide +kernel
theorem flow01 : WindowCurvatureFlow.check cell01 edges01 direction01 rows01 = true := by
 decide +kernel
theorem exclude01 {g : Fin 9 → ℝ}
 (hg : WindowMinimizerCover.Relevant ((123:ℝ)/128) g)
 (hcell : WindowDifferenceCell.Contains cell01 g) : False :=
 WindowCurvatureScalar.exclude scalar01 support01 flow01 hg hcell
set_option pp.fullNames true
#print axioms scalar01
#print axioms support01
#print axioms flow01
#print axioms exclude01
end StructuralGoal20261016.WindowCurvatureLeaves
