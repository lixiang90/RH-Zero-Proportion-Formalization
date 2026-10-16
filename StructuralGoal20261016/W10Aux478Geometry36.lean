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
theorem normalized288 : AdaptiveCoverage.normalize SL cell576 = normal564 := by
  calc
    AdaptiveCoverage.normalize SL cell576 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell576)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell576)).symm
    _ = normal564 := by rfl
theorem left288 : leftChild 9 PR SL normal564 3 6 114688 = cell577 := by
  calc
    leftChild 9 PR SL normal564 3 6 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal564) 3 6 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal564) 3 6 114688).symm
    _ = cell577 := by rfl
theorem right288 : rightChild 9 PR SL normal564 3 6 114688 = cell578 := by
  calc
    rightChild 9 PR SL normal564 3 6 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal564) 3 6 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal564) 3 6 114688).symm
    _ = cell578 := by rfl
theorem normalized289 : AdaptiveCoverage.normalize SL cell577 = normal565 := by
  calc
    AdaptiveCoverage.normalize SL cell577 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell577)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell577)).symm
    _ = normal565 := by rfl
theorem left289 : leftChild 9 PR SL normal565 2 5 114688 = cell579 := by
  calc
    leftChild 9 PR SL normal565 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal565) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal565) 2 5 114688).symm
    _ = cell579 := by rfl
theorem right289 : rightChild 9 PR SL normal565 2 5 114688 = cell580 := by
  calc
    rightChild 9 PR SL normal565 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal565) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal565) 2 5 114688).symm
    _ = cell580 := by rfl
theorem normalized290 : AdaptiveCoverage.normalize SL cell579 = normal566 := by
  calc
    AdaptiveCoverage.normalize SL cell579 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell579)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell579)).symm
    _ = normal566 := by rfl
theorem left290 : leftChild 9 PR SL normal566 4 7 114688 = cell581 := by
  calc
    leftChild 9 PR SL normal566 4 7 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal566) 4 7 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal566) 4 7 114688).symm
    _ = cell581 := by rfl
theorem right290 : rightChild 9 PR SL normal566 4 7 114688 = cell582 := by
  calc
    rightChild 9 PR SL normal566 4 7 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal566) 4 7 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal566) 4 7 114688).symm
    _ = cell582 := by rfl
theorem normalized291 : AdaptiveCoverage.normalize SL cell574 = normal571 := by
  calc
    AdaptiveCoverage.normalize SL cell574 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell574)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell574)).symm
    _ = normal571 := by rfl
theorem left291 : leftChild 9 PR SL normal571 1 9 294912 = cell583 := by
  calc
    leftChild 9 PR SL normal571 1 9 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal571) 1 9 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal571) 1 9 294912).symm
    _ = cell583 := by rfl
theorem right291 : rightChild 9 PR SL normal571 1 9 294912 = cell584 := by
  calc
    rightChild 9 PR SL normal571 1 9 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal571) 1 9 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal571) 1 9 294912).symm
    _ = cell584 := by rfl
theorem normalized292 : AdaptiveCoverage.normalize SL cell583 = normal572 := by
  calc
    AdaptiveCoverage.normalize SL cell583 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell583)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell583)).symm
    _ = normal572 := by rfl
theorem left292 : leftChild 9 PR SL normal572 3 6 114688 = cell585 := by
  calc
    leftChild 9 PR SL normal572 3 6 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal572) 3 6 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal572) 3 6 114688).symm
    _ = cell585 := by rfl
theorem right292 : rightChild 9 PR SL normal572 3 6 114688 = cell586 := by
  calc
    rightChild 9 PR SL normal572 3 6 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal572) 3 6 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal572) 3 6 114688).symm
    _ = cell586 := by rfl
theorem normalized293 : AdaptiveCoverage.normalize SL cell585 = normal573 := by
  calc
    AdaptiveCoverage.normalize SL cell585 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell585)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell585)).symm
    _ = normal573 := by rfl
theorem left293 : leftChild 9 PR SL normal573 2 5 114688 = cell587 := by
  calc
    leftChild 9 PR SL normal573 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal573) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal573) 2 5 114688).symm
    _ = cell587 := by rfl
theorem right293 : rightChild 9 PR SL normal573 2 5 114688 = cell588 := by
  calc
    rightChild 9 PR SL normal573 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal573) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal573) 2 5 114688).symm
    _ = cell588 := by rfl
theorem normalized294 : AdaptiveCoverage.normalize SL cell584 = normal577 := by
  calc
    AdaptiveCoverage.normalize SL cell584 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell584)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell584)).symm
    _ = normal577 := by rfl
theorem left294 : leftChild 9 PR SL normal577 3 6 114688 = cell589 := by
  calc
    leftChild 9 PR SL normal577 3 6 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal577) 3 6 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal577) 3 6 114688).symm
    _ = cell589 := by rfl
theorem right294 : rightChild 9 PR SL normal577 3 6 114688 = cell590 := by
  calc
    rightChild 9 PR SL normal577 3 6 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal577) 3 6 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal577) 3 6 114688).symm
    _ = cell590 := by rfl
theorem normalized295 : AdaptiveCoverage.normalize SL cell589 = normal578 := by
  calc
    AdaptiveCoverage.normalize SL cell589 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell589)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell589)).symm
    _ = normal578 := by rfl
theorem left295 : leftChild 9 PR SL normal578 2 5 114688 = cell591 := by
  calc
    leftChild 9 PR SL normal578 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal578) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal578) 2 5 114688).symm
    _ = cell591 := by rfl
theorem right295 : rightChild 9 PR SL normal578 2 5 114688 = cell592 := by
  calc
    rightChild 9 PR SL normal578 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal578) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal578) 2 5 114688).symm
    _ = cell592 := by rfl

set_option pp.fullNames true
#print axioms normalized288
#print axioms left288
#print axioms right288
#print axioms normalized289
#print axioms left289
#print axioms right289
#print axioms normalized290
#print axioms left290
#print axioms right290
#print axioms normalized291
#print axioms left291
#print axioms right291
#print axioms normalized292
#print axioms left292
#print axioms right292
#print axioms normalized293
#print axioms left293
#print axioms right293
#print axioms normalized294
#print axioms left294
#print axioms right294
#print axioms normalized295
#print axioms left295
#print axioms right295
end StructuralGoal20261016.W10Aux478
end
