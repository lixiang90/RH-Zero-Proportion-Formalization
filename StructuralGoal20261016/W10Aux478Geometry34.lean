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
theorem normalized272 : AdaptiveCoverage.normalize SL cell544 = normal533 := by
  calc
    AdaptiveCoverage.normalize SL cell544 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell544)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell544)).symm
    _ = normal533 := by rfl
theorem left272 : leftChild 9 PR SL normal533 4 7 98304 = cell545 := by
  calc
    leftChild 9 PR SL normal533 4 7 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal533) 4 7 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal533) 4 7 98304).symm
    _ = cell545 := by rfl
theorem right272 : rightChild 9 PR SL normal533 4 7 98304 = cell546 := by
  calc
    rightChild 9 PR SL normal533 4 7 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal533) 4 7 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal533) 4 7 98304).symm
    _ = cell546 := by rfl
theorem normalized273 : AdaptiveCoverage.normalize SL cell546 = normal535 := by
  calc
    AdaptiveCoverage.normalize SL cell546 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell546)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell546)).symm
    _ = normal535 := by rfl
theorem left273 : leftChild 9 PR SL normal535 1 8 262144 = cell547 := by
  calc
    leftChild 9 PR SL normal535 1 8 262144 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal535) 1 8 262144).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal535) 1 8 262144).symm
    _ = cell547 := by rfl
theorem right273 : rightChild 9 PR SL normal535 1 8 262144 = cell548 := by
  calc
    rightChild 9 PR SL normal535 1 8 262144 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal535) 1 8 262144).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal535) 1 8 262144).symm
    _ = cell548 := by rfl
theorem normalized274 : AdaptiveCoverage.normalize SL cell548 = normal537 := by
  calc
    AdaptiveCoverage.normalize SL cell548 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell548)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell548)).symm
    _ = normal537 := by rfl
theorem left274 : leftChild 9 PR SL normal537 0 6 245760 = cell549 := by
  calc
    leftChild 9 PR SL normal537 0 6 245760 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal537) 0 6 245760).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal537) 0 6 245760).symm
    _ = cell549 := by rfl
theorem right274 : rightChild 9 PR SL normal537 0 6 245760 = cell550 := by
  calc
    rightChild 9 PR SL normal537 0 6 245760 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal537) 0 6 245760).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal537) 0 6 245760).symm
    _ = cell550 := by rfl
theorem normalized275 : AdaptiveCoverage.normalize SL cell549 = normal538 := by
  calc
    AdaptiveCoverage.normalize SL cell549 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell549)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell549)).symm
    _ = normal538 := by rfl
theorem left275 : leftChild 9 PR SL normal538 0 7 278528 = cell551 := by
  calc
    leftChild 9 PR SL normal538 0 7 278528 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal538) 0 7 278528).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal538) 0 7 278528).symm
    _ = cell551 := by rfl
theorem right275 : rightChild 9 PR SL normal538 0 7 278528 = cell552 := by
  calc
    rightChild 9 PR SL normal538 0 7 278528 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal538) 0 7 278528).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal538) 0 7 278528).symm
    _ = cell552 := by rfl
theorem normalized276 : AdaptiveCoverage.normalize SL cell540 = normal542 := by
  calc
    AdaptiveCoverage.normalize SL cell540 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell540)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell540)).symm
    _ = normal542 := by rfl
theorem left276 : leftChild 9 PR SL normal542 2 6 147456 = cell553 := by
  calc
    leftChild 9 PR SL normal542 2 6 147456 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal542) 2 6 147456).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal542) 2 6 147456).symm
    _ = cell553 := by rfl
theorem right276 : rightChild 9 PR SL normal542 2 6 147456 = cell554 := by
  calc
    rightChild 9 PR SL normal542 2 6 147456 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal542) 2 6 147456).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal542) 2 6 147456).symm
    _ = cell554 := by rfl
theorem normalized277 : AdaptiveCoverage.normalize SL cell554 = normal544 := by
  calc
    AdaptiveCoverage.normalize SL cell554 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell554)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell554)).symm
    _ = normal544 := by rfl
theorem left277 : leftChild 9 PR SL normal544 3 6 98304 = cell555 := by
  calc
    leftChild 9 PR SL normal544 3 6 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal544) 3 6 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal544) 3 6 98304).symm
    _ = cell555 := by rfl
theorem right277 : rightChild 9 PR SL normal544 3 6 98304 = cell556 := by
  calc
    rightChild 9 PR SL normal544 3 6 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal544) 3 6 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal544) 3 6 98304).symm
    _ = cell556 := by rfl
theorem normalized278 : AdaptiveCoverage.normalize SL cell556 = normal546 := by
  calc
    AdaptiveCoverage.normalize SL cell556 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell556)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell556)).symm
    _ = normal546 := by rfl
theorem left278 : leftChild 9 PR SL normal546 2 5 114688 = cell557 := by
  calc
    leftChild 9 PR SL normal546 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal546) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal546) 2 5 114688).symm
    _ = cell557 := by rfl
theorem right278 : rightChild 9 PR SL normal546 2 5 114688 = cell558 := by
  calc
    rightChild 9 PR SL normal546 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal546) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal546) 2 5 114688).symm
    _ = cell558 := by rfl
theorem normalized279 : AdaptiveCoverage.normalize SL cell558 = normal548 := by
  calc
    AdaptiveCoverage.normalize SL cell558 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell558)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell558)).symm
    _ = normal548 := by rfl
theorem left279 : leftChild 9 PR SL normal548 4 7 114688 = cell559 := by
  calc
    leftChild 9 PR SL normal548 4 7 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal548) 4 7 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal548) 4 7 114688).symm
    _ = cell559 := by rfl
theorem right279 : rightChild 9 PR SL normal548 4 7 114688 = cell560 := by
  calc
    rightChild 9 PR SL normal548 4 7 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal548) 4 7 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal548) 4 7 114688).symm
    _ = cell560 := by rfl

set_option pp.fullNames true
#print axioms normalized272
#print axioms left272
#print axioms right272
#print axioms normalized273
#print axioms left273
#print axioms right273
#print axioms normalized274
#print axioms left274
#print axioms right274
#print axioms normalized275
#print axioms left275
#print axioms right275
#print axioms normalized276
#print axioms left276
#print axioms right276
#print axioms normalized277
#print axioms left277
#print axioms right277
#print axioms normalized278
#print axioms left278
#print axioms right278
#print axioms normalized279
#print axioms left279
#print axioms right279
end StructuralGoal20261016.W10Aux478
end
