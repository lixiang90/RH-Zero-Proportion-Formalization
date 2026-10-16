/- SPDX-License-Identifier: Apache-2.0
Actual second-variation exclusion on frozen cell r0010000011011011100011100.
This is local to that cell and does not assert completion of a global cover.
-/
import StructuralGoal20261016.WindowCurvatureLeafData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowCurvatureLeaves
open WindowCurvatureLeafData
theorem scalar00 : WindowCurvatureScalar.allCheck cell00 rows00 packets00 = true := by
 decide +kernel
theorem support00 : WindowCurvatureScalar.supportCheck cell00 direction00 = true := by
 decide +kernel
theorem flow00 : WindowCurvatureFlow.check cell00 edges00 direction00 rows00 = true := by
 decide +kernel
theorem exclude00 {g : Fin 9 → ℝ}
 (hg : WindowMinimizerCover.Relevant ((123:ℝ)/128) g)
 (hcell : WindowDifferenceCell.Contains cell00 g) : False :=
 WindowCurvatureScalar.exclude scalar00 support00 flow00 hg hcell
set_option pp.fullNames true
#print axioms scalar00
#print axioms support00
#print axioms flow00
#print axioms exclude00
end StructuralGoal20261016.WindowCurvatureLeaves
