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
theorem normalized256 : AdaptiveCoverage.normalize SL cell511 = normal503 := by
  calc
    AdaptiveCoverage.normalize SL cell511 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell511)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell511)).symm
    _ = normal503 := by rfl
theorem left256 : leftChild 9 PR SL normal503 3 5 81920 = cell513 := by
  calc
    leftChild 9 PR SL normal503 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal503) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal503) 3 5 81920).symm
    _ = cell513 := by rfl
theorem right256 : rightChild 9 PR SL normal503 3 5 81920 = cell514 := by
  calc
    rightChild 9 PR SL normal503 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal503) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal503) 3 5 81920).symm
    _ = cell514 := by rfl
theorem normalized257 : AdaptiveCoverage.normalize SL cell513 = normal504 := by
  calc
    AdaptiveCoverage.normalize SL cell513 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell513)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell513)).symm
    _ = normal504 := by rfl
theorem left257 : leftChild 9 PR SL normal504 4 6 81920 = cell515 := by
  calc
    leftChild 9 PR SL normal504 4 6 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal504) 4 6 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal504) 4 6 81920).symm
    _ = cell515 := by rfl
theorem right257 : rightChild 9 PR SL normal504 4 6 81920 = cell516 := by
  calc
    rightChild 9 PR SL normal504 4 6 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal504) 4 6 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal504) 4 6 81920).symm
    _ = cell516 := by rfl
theorem normalized258 : AdaptiveCoverage.normalize SL cell515 = normal505 := by
  calc
    AdaptiveCoverage.normalize SL cell515 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell515)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell515)).symm
    _ = normal505 := by rfl
theorem left258 : leftChild 9 PR SL normal505 0 9 335872 = cell517 := by
  calc
    leftChild 9 PR SL normal505 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal505) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal505) 0 9 335872).symm
    _ = cell517 := by rfl
theorem right258 : rightChild 9 PR SL normal505 0 9 335872 = cell518 := by
  calc
    rightChild 9 PR SL normal505 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal505) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal505) 0 9 335872).symm
    _ = cell518 := by rfl
theorem normalized259 : AdaptiveCoverage.normalize SL cell517 = normal506 := by
  calc
    AdaptiveCoverage.normalize SL cell517 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell517)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell517)).symm
    _ = normal506 := by rfl
theorem left259 : leftChild 9 PR SL normal506 2 5 114688 = cell519 := by
  calc
    leftChild 9 PR SL normal506 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal506) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal506) 2 5 114688).symm
    _ = cell519 := by rfl
theorem right259 : rightChild 9 PR SL normal506 2 5 114688 = cell520 := by
  calc
    rightChild 9 PR SL normal506 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal506) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal506) 2 5 114688).symm
    _ = cell520 := by rfl
theorem normalized260 : AdaptiveCoverage.normalize SL cell512 = normal512 := by
  calc
    AdaptiveCoverage.normalize SL cell512 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell512)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell512)).symm
    _ = normal512 := by rfl
theorem left260 : leftChild 9 PR SL normal512 3 5 81920 = cell521 := by
  calc
    leftChild 9 PR SL normal512 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal512) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal512) 3 5 81920).symm
    _ = cell521 := by rfl
theorem right260 : rightChild 9 PR SL normal512 3 5 81920 = cell522 := by
  calc
    rightChild 9 PR SL normal512 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal512) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal512) 3 5 81920).symm
    _ = cell522 := by rfl
theorem normalized261 : AdaptiveCoverage.normalize SL cell521 = normal513 := by
  calc
    AdaptiveCoverage.normalize SL cell521 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell521)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell521)).symm
    _ = normal513 := by rfl
theorem left261 : leftChild 9 PR SL normal513 4 6 81920 = cell523 := by
  calc
    leftChild 9 PR SL normal513 4 6 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal513) 4 6 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal513) 4 6 81920).symm
    _ = cell523 := by rfl
theorem right261 : rightChild 9 PR SL normal513 4 6 81920 = cell524 := by
  calc
    rightChild 9 PR SL normal513 4 6 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal513) 4 6 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal513) 4 6 81920).symm
    _ = cell524 := by rfl
theorem normalized262 : AdaptiveCoverage.normalize SL cell523 = normal514 := by
  calc
    AdaptiveCoverage.normalize SL cell523 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell523)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell523)).symm
    _ = normal514 := by rfl
theorem left262 : leftChild 9 PR SL normal514 0 9 335872 = cell525 := by
  calc
    leftChild 9 PR SL normal514 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal514) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal514) 0 9 335872).symm
    _ = cell525 := by rfl
theorem right262 : rightChild 9 PR SL normal514 0 9 335872 = cell526 := by
  calc
    rightChild 9 PR SL normal514 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal514) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal514) 0 9 335872).symm
    _ = cell526 := by rfl
theorem normalized263 : AdaptiveCoverage.normalize SL cell525 = normal515 := by
  calc
    AdaptiveCoverage.normalize SL cell525 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell525)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell525)).symm
    _ = normal515 := by rfl
theorem left263 : leftChild 9 PR SL normal515 2 5 114688 = cell527 := by
  calc
    leftChild 9 PR SL normal515 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal515) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal515) 2 5 114688).symm
    _ = cell527 := by rfl
theorem right263 : rightChild 9 PR SL normal515 2 5 114688 = cell528 := by
  calc
    rightChild 9 PR SL normal515 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal515) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal515) 2 5 114688).symm
    _ = cell528 := by rfl

set_option pp.fullNames true
#print axioms normalized256
#print axioms left256
#print axioms right256
#print axioms normalized257
#print axioms left257
#print axioms right257
#print axioms normalized258
#print axioms left258
#print axioms right258
#print axioms normalized259
#print axioms left259
#print axioms right259
#print axioms normalized260
#print axioms left260
#print axioms right260
#print axioms normalized261
#print axioms left261
#print axioms right261
#print axioms normalized262
#print axioms left262
#print axioms right262
#print axioms normalized263
#print axioms left263
#print axioms right263
end StructuralGoal20261016.W10Aux478
end
