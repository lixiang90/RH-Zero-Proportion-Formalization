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
theorem normalized232 : AdaptiveCoverage.normalize SL cell463 = normal452 := by
  calc
    AdaptiveCoverage.normalize SL cell463 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell463)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell463)).symm
    _ = normal452 := by rfl
theorem left232 : leftChild 9 PR SL normal452 2 5 114688 = cell465 := by
  calc
    leftChild 9 PR SL normal452 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal452) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal452) 2 5 114688).symm
    _ = cell465 := by rfl
theorem right232 : rightChild 9 PR SL normal452 2 5 114688 = cell466 := by
  calc
    rightChild 9 PR SL normal452 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal452) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal452) 2 5 114688).symm
    _ = cell466 := by rfl
theorem normalized233 : AdaptiveCoverage.normalize SL cell466 = normal454 := by
  calc
    AdaptiveCoverage.normalize SL cell466 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell466)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell466)).symm
    _ = normal454 := by rfl
theorem left233 : leftChild 9 PR SL normal454 2 4 81920 = cell467 := by
  calc
    leftChild 9 PR SL normal454 2 4 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal454) 2 4 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal454) 2 4 81920).symm
    _ = cell467 := by rfl
theorem right233 : rightChild 9 PR SL normal454 2 4 81920 = cell468 := by
  calc
    rightChild 9 PR SL normal454 2 4 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal454) 2 4 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal454) 2 4 81920).symm
    _ = cell468 := by rfl
theorem normalized234 : AdaptiveCoverage.normalize SL cell462 = normal458 := by
  calc
    AdaptiveCoverage.normalize SL cell462 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell462)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell462)).symm
    _ = normal458 := by rfl
theorem left234 : leftChild 9 PR SL normal458 0 9 335872 = cell469 := by
  calc
    leftChild 9 PR SL normal458 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal458) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal458) 0 9 335872).symm
    _ = cell469 := by rfl
theorem right234 : rightChild 9 PR SL normal458 0 9 335872 = cell470 := by
  calc
    rightChild 9 PR SL normal458 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal458) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal458) 0 9 335872).symm
    _ = cell470 := by rfl
theorem normalized235 : AdaptiveCoverage.normalize SL cell469 = normal459 := by
  calc
    AdaptiveCoverage.normalize SL cell469 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell469)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell469)).symm
    _ = normal459 := by rfl
theorem left235 : leftChild 9 PR SL normal459 2 5 114688 = cell471 := by
  calc
    leftChild 9 PR SL normal459 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal459) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal459) 2 5 114688).symm
    _ = cell471 := by rfl
theorem right235 : rightChild 9 PR SL normal459 2 5 114688 = cell472 := by
  calc
    rightChild 9 PR SL normal459 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal459) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal459) 2 5 114688).symm
    _ = cell472 := by rfl
theorem normalized236 : AdaptiveCoverage.normalize SL cell472 = normal461 := by
  calc
    AdaptiveCoverage.normalize SL cell472 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell472)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell472)).symm
    _ = normal461 := by rfl
theorem left236 : leftChild 9 PR SL normal461 4 7 98304 = cell473 := by
  calc
    leftChild 9 PR SL normal461 4 7 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal461) 4 7 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal461) 4 7 98304).symm
    _ = cell473 := by rfl
theorem right236 : rightChild 9 PR SL normal461 4 7 98304 = cell474 := by
  calc
    rightChild 9 PR SL normal461 4 7 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal461) 4 7 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal461) 4 7 98304).symm
    _ = cell474 := by rfl
theorem normalized237 : AdaptiveCoverage.normalize SL cell474 = normal463 := by
  calc
    AdaptiveCoverage.normalize SL cell474 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell474)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell474)).symm
    _ = normal463 := by rfl
theorem left237 : leftChild 9 PR SL normal463 3 5 65536 = cell475 := by
  calc
    leftChild 9 PR SL normal463 3 5 65536 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal463) 3 5 65536).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal463) 3 5 65536).symm
    _ = cell475 := by rfl
theorem right237 : rightChild 9 PR SL normal463 3 5 65536 = cell476 := by
  calc
    rightChild 9 PR SL normal463 3 5 65536 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal463) 3 5 65536).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal463) 3 5 65536).symm
    _ = cell476 := by rfl
theorem normalized238 : AdaptiveCoverage.normalize SL cell476 = normal465 := by
  calc
    AdaptiveCoverage.normalize SL cell476 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell476)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell476)).symm
    _ = normal465 := by rfl
theorem left238 : leftChild 9 PR SL normal465 4 6 65536 = cell477 := by
  calc
    leftChild 9 PR SL normal465 4 6 65536 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal465) 4 6 65536).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal465) 4 6 65536).symm
    _ = cell477 := by rfl
theorem right238 : rightChild 9 PR SL normal465 4 6 65536 = cell478 := by
  calc
    rightChild 9 PR SL normal465 4 6 65536 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal465) 4 6 65536).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal465) 4 6 65536).symm
    _ = cell478 := by rfl
theorem normalized239 : AdaptiveCoverage.normalize SL cell478 = normal467 := by
  calc
    AdaptiveCoverage.normalize SL cell478 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell478)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell478)).symm
    _ = normal467 := by rfl
theorem left239 : leftChild 9 PR SL normal467 0 7 262144 = cell479 := by
  calc
    leftChild 9 PR SL normal467 0 7 262144 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal467) 0 7 262144).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal467) 0 7 262144).symm
    _ = cell479 := by rfl
theorem right239 : rightChild 9 PR SL normal467 0 7 262144 = cell480 := by
  calc
    rightChild 9 PR SL normal467 0 7 262144 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal467) 0 7 262144).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal467) 0 7 262144).symm
    _ = cell480 := by rfl

set_option pp.fullNames true
#print axioms normalized232
#print axioms left232
#print axioms right232
#print axioms normalized233
#print axioms left233
#print axioms right233
#print axioms normalized234
#print axioms left234
#print axioms right234
#print axioms normalized235
#print axioms left235
#print axioms right235
#print axioms normalized236
#print axioms left236
#print axioms right236
#print axioms normalized237
#print axioms left237
#print axioms right237
#print axioms normalized238
#print axioms left238
#print axioms right238
#print axioms normalized239
#print axioms left239
#print axioms right239
end StructuralGoal20261016.W10Aux478
end
