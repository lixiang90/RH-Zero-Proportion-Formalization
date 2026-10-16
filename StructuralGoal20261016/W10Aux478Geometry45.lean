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
theorem normalized360 : AdaptiveCoverage.normalize SL cell720 = normal712 := by
  calc
    AdaptiveCoverage.normalize SL cell720 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell720)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell720)).symm
    _ = normal712 := by rfl
theorem left360 : leftChild 9 PR SL normal712 0 9 338990 = cell721 := by
  calc
    leftChild 9 PR SL normal712 0 9 338990 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal712) 0 9 338990).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal712) 0 9 338990).symm
    _ = cell721 := by rfl
theorem right360 : rightChild 9 PR SL normal712 0 9 338990 = cell722 := by
  calc
    rightChild 9 PR SL normal712 0 9 338990 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal712) 0 9 338990).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal712) 0 9 338990).symm
    _ = cell722 := by rfl
theorem normalized361 : AdaptiveCoverage.normalize SL cell680 = normal716 := by
  calc
    AdaptiveCoverage.normalize SL cell680 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell680)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell680)).symm
    _ = normal716 := by rfl
theorem left361 : leftChild 9 PR SL normal716 4 7 103376 = cell723 := by
  calc
    leftChild 9 PR SL normal716 4 7 103376 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal716) 4 7 103376).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal716) 4 7 103376).symm
    _ = cell723 := by rfl
theorem right361 : rightChild 9 PR SL normal716 4 7 103376 = cell724 := by
  calc
    rightChild 9 PR SL normal716 4 7 103376 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal716) 4 7 103376).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal716) 4 7 103376).symm
    _ = cell724 := by rfl
theorem normalized362 : AdaptiveCoverage.normalize SL cell723 = normal717 := by
  calc
    AdaptiveCoverage.normalize SL cell723 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell723)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell723)).symm
    _ = normal717 := by rfl
theorem left362 : leftChild 9 PR SL normal717 0 6 235824 = cell725 := by
  calc
    leftChild 9 PR SL normal717 0 6 235824 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal717) 0 6 235824).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal717) 0 6 235824).symm
    _ = cell725 := by rfl
theorem right362 : rightChild 9 PR SL normal717 0 6 235824 = cell726 := by
  calc
    rightChild 9 PR SL normal717 0 6 235824 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal717) 0 6 235824).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal717) 0 6 235824).symm
    _ = cell726 := by rfl
theorem normalized363 : AdaptiveCoverage.normalize SL cell726 = normal719 := by
  calc
    AdaptiveCoverage.normalize SL cell726 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell726)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell726)).symm
    _ = normal719 := by rfl
theorem left363 : leftChild 9 PR SL normal719 0 6 248166 = cell727 := by
  calc
    leftChild 9 PR SL normal719 0 6 248166 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal719) 0 6 248166).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal719) 0 6 248166).symm
    _ = cell727 := by rfl
theorem right363 : rightChild 9 PR SL normal719 0 6 248166 = cell728 := by
  calc
    rightChild 9 PR SL normal719 0 6 248166 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal719) 0 6 248166).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal719) 0 6 248166).symm
    _ = cell728 := by rfl
theorem normalized364 : AdaptiveCoverage.normalize SL cell727 = normal720 := by
  calc
    AdaptiveCoverage.normalize SL cell727 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell727)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell727)).symm
    _ = normal720 := by rfl
theorem left364 : leftChild 9 PR SL normal720 0 8 303696 = cell729 := by
  calc
    leftChild 9 PR SL normal720 0 8 303696 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal720) 0 8 303696).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal720) 0 8 303696).symm
    _ = cell729 := by rfl
theorem right364 : rightChild 9 PR SL normal720 0 8 303696 = cell730 := by
  calc
    rightChild 9 PR SL normal720 0 8 303696 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal720) 0 8 303696).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal720) 0 8 303696).symm
    _ = cell730 := by rfl
theorem normalized365 : AdaptiveCoverage.normalize SL cell730 = normal722 := by
  calc
    AdaptiveCoverage.normalize SL cell730 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell730)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell730)).symm
    _ = normal722 := by rfl
theorem left365 : leftChild 9 PR SL normal722 0 9 341264 = cell731 := by
  calc
    leftChild 9 PR SL normal722 0 9 341264 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal722) 0 9 341264).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal722) 0 9 341264).symm
    _ = cell731 := by rfl
theorem right365 : rightChild 9 PR SL normal722 0 9 341264 = cell732 := by
  calc
    rightChild 9 PR SL normal722 0 9 341264 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal722) 0 9 341264).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal722) 0 9 341264).symm
    _ = cell732 := by rfl
theorem normalized366 : AdaptiveCoverage.normalize SL cell724 = normal726 := by
  calc
    AdaptiveCoverage.normalize SL cell724 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell724)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell724)).symm
    _ = normal726 := by rfl
theorem left366 : leftChild 9 PR SL normal726 3 9 236832 = cell733 := by
  calc
    leftChild 9 PR SL normal726 3 9 236832 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal726) 3 9 236832).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal726) 3 9 236832).symm
    _ = cell733 := by rfl
theorem right366 : rightChild 9 PR SL normal726 3 9 236832 = cell734 := by
  calc
    rightChild 9 PR SL normal726 3 9 236832 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal726) 3 9 236832).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal726) 3 9 236832).symm
    _ = cell734 := by rfl
theorem normalized367 : AdaptiveCoverage.normalize SL cell734 = normal728 := by
  calc
    AdaptiveCoverage.normalize SL cell734 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell734)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell734)).symm
    _ = normal728 := by rfl
theorem left367 : leftChild 9 PR SL normal728 3 9 248670 = cell735 := by
  calc
    leftChild 9 PR SL normal728 3 9 248670 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal728) 3 9 248670).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal728) 3 9 248670).symm
    _ = cell735 := by rfl
theorem right367 : rightChild 9 PR SL normal728 3 9 248670 = cell736 := by
  calc
    rightChild 9 PR SL normal728 3 9 248670 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal728) 3 9 248670).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal728) 3 9 248670).symm
    _ = cell736 := by rfl

set_option pp.fullNames true
#print axioms normalized360
#print axioms left360
#print axioms right360
#print axioms normalized361
#print axioms left361
#print axioms right361
#print axioms normalized362
#print axioms left362
#print axioms right362
#print axioms normalized363
#print axioms left363
#print axioms right363
#print axioms normalized364
#print axioms left364
#print axioms right364
#print axioms normalized365
#print axioms left365
#print axioms right365
#print axioms normalized366
#print axioms left366
#print axioms right366
#print axioms normalized367
#print axioms left367
#print axioms right367
end StructuralGoal20261016.W10Aux478
end
