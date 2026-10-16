/- Frozen 478-leaf W10 subtree; complete global coverage is not asserted. -/
import StructuralGoal20261016.W10Aux478Data
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
open StructuralW10Cert20261016.TreeCoverage
open StructuralGoal20261016.LeanCoverBase
open StructuralW10Unconditional20261016
open StructuralW10Cert20261016
namespace StructuralGoal20261016.W10Aux478
theorem normalized264 : AdaptiveCoverage.normalize SL cell528 = normal517 := by
  calc
    AdaptiveCoverage.normalize SL cell528 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell528)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell528)).symm
    _ = normal517 := by rfl
theorem left264 : leftChild 9 PR SL normal517 3 6 98304 = cell529 := by
  calc
    leftChild 9 PR SL normal517 3 6 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal517) 3 6 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal517) 3 6 98304).symm
    _ = cell529 := by rfl
theorem right264 : rightChild 9 PR SL normal517 3 6 98304 = cell530 := by
  calc
    rightChild 9 PR SL normal517 3 6 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal517) 3 6 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal517) 3 6 98304).symm
    _ = cell530 := by rfl
theorem normalized265 : AdaptiveCoverage.normalize SL cell530 = normal519 := by
  calc
    AdaptiveCoverage.normalize SL cell530 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell530)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell530)).symm
    _ = normal519 := by rfl
theorem left265 : leftChild 9 PR SL normal519 4 7 98304 = cell531 := by
  calc
    leftChild 9 PR SL normal519 4 7 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal519) 4 7 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal519) 4 7 98304).symm
    _ = cell531 := by rfl
theorem right265 : rightChild 9 PR SL normal519 4 7 98304 = cell532 := by
  calc
    rightChild 9 PR SL normal519 4 7 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal519) 4 7 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal519) 4 7 98304).symm
    _ = cell532 := by rfl
theorem normalized266 : AdaptiveCoverage.normalize SL cell532 = normal521 := by
  calc
    AdaptiveCoverage.normalize SL cell532 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell532)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell532)).symm
    _ = normal521 := by rfl
theorem left266 : leftChild 9 PR SL normal521 2 4 81920 = cell533 := by
  calc
    leftChild 9 PR SL normal521 2 4 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal521) 2 4 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal521) 2 4 81920).symm
    _ = cell533 := by rfl
theorem right266 : rightChild 9 PR SL normal521 2 4 81920 = cell534 := by
  calc
    rightChild 9 PR SL normal521 2 4 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal521) 2 4 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal521) 2 4 81920).symm
    _ = cell534 := by rfl
theorem normalized267 : AdaptiveCoverage.normalize SL cell534 = normal523 := by
  calc
    AdaptiveCoverage.normalize SL cell534 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell534)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell534)).symm
    _ = normal523 := by rfl
theorem left267 : leftChild 9 PR SL normal523 5 7 81920 = cell535 := by
  calc
    leftChild 9 PR SL normal523 5 7 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal523) 5 7 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal523) 5 7 81920).symm
    _ = cell535 := by rfl
theorem right267 : rightChild 9 PR SL normal523 5 7 81920 = cell536 := by
  calc
    rightChild 9 PR SL normal523 5 7 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal523) 5 7 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal523) 5 7 81920).symm
    _ = cell536 := by rfl
theorem normalized268 : AdaptiveCoverage.normalize SL cell535 = normal524 := by
  calc
    AdaptiveCoverage.normalize SL cell535 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell535)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell535)).symm
    _ = normal524 := by rfl
theorem left268 : leftChild 9 PR SL normal524 3 7 147456 = cell537 := by
  calc
    leftChild 9 PR SL normal524 3 7 147456 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal524) 3 7 147456).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal524) 3 7 147456).symm
    _ = cell537 := by rfl
theorem right268 : rightChild 9 PR SL normal524 3 7 147456 = cell538 := by
  calc
    rightChild 9 PR SL normal524 3 7 147456 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal524) 3 7 147456).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal524) 3 7 147456).symm
    _ = cell538 := by rfl
theorem normalized269 : AdaptiveCoverage.normalize SL cell526 = normal528 := by
  calc
    AdaptiveCoverage.normalize SL cell526 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell526)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell526)).symm
    _ = normal528 := by rfl
theorem left269 : leftChild 9 PR SL normal528 2 7 196608 = cell539 := by
  calc
    leftChild 9 PR SL normal528 2 7 196608 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal528) 2 7 196608).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal528) 2 7 196608).symm
    _ = cell539 := by rfl
theorem right269 : rightChild 9 PR SL normal528 2 7 196608 = cell540 := by
  calc
    rightChild 9 PR SL normal528 2 7 196608 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal528) 2 7 196608).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal528) 2 7 196608).symm
    _ = cell540 := by rfl
theorem normalized270 : AdaptiveCoverage.normalize SL cell539 = normal529 := by
  calc
    AdaptiveCoverage.normalize SL cell539 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell539)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell539)).symm
    _ = normal529 := by rfl
theorem left270 : leftChild 9 PR SL normal529 2 5 114688 = cell541 := by
  calc
    leftChild 9 PR SL normal529 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal529) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal529) 2 5 114688).symm
    _ = cell541 := by rfl
theorem right270 : rightChild 9 PR SL normal529 2 5 114688 = cell542 := by
  calc
    rightChild 9 PR SL normal529 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal529) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal529) 2 5 114688).symm
    _ = cell542 := by rfl
theorem normalized271 : AdaptiveCoverage.normalize SL cell542 = normal531 := by
  calc
    AdaptiveCoverage.normalize SL cell542 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell542)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell542)).symm
    _ = normal531 := by rfl
theorem left271 : leftChild 9 PR SL normal531 3 6 98304 = cell543 := by
  calc
    leftChild 9 PR SL normal531 3 6 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal531) 3 6 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal531) 3 6 98304).symm
    _ = cell543 := by rfl
theorem right271 : rightChild 9 PR SL normal531 3 6 98304 = cell544 := by
  calc
    rightChild 9 PR SL normal531 3 6 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal531) 3 6 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal531) 3 6 98304).symm
    _ = cell544 := by rfl

set_option pp.fullNames true
#print axioms normalized264
#print axioms left264
#print axioms right264
#print axioms normalized265
#print axioms left265
#print axioms right265
#print axioms normalized266
#print axioms left266
#print axioms right266
#print axioms normalized267
#print axioms left267
#print axioms right267
#print axioms normalized268
#print axioms left268
#print axioms right268
#print axioms normalized269
#print axioms left269
#print axioms right269
#print axioms normalized270
#print axioms left270
#print axioms right270
#print axioms normalized271
#print axioms left271
#print axioms right271
end StructuralGoal20261016.W10Aux478
end
