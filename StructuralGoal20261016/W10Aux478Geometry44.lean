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
theorem normalized352 : AdaptiveCoverage.normalize SL cell704 = normal696 := by
  calc
    AdaptiveCoverage.normalize SL cell704 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell704)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell704)).symm
    _ = normal696 := by rfl
theorem left352 : leftChild 9 PR SL normal696 3 9 248166 = cell705 := by
  calc
    leftChild 9 PR SL normal696 3 9 248166 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal696) 3 9 248166).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal696) 3 9 248166).symm
    _ = cell705 := by rfl
theorem right352 : rightChild 9 PR SL normal696 3 9 248166 = cell706 := by
  calc
    rightChild 9 PR SL normal696 3 9 248166 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal696) 3 9 248166).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal696) 3 9 248166).symm
    _ = cell706 := by rfl
theorem normalized353 : AdaptiveCoverage.normalize SL cell705 = normal697 := by
  calc
    AdaptiveCoverage.normalize SL cell705 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell705)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell705)).symm
    _ = normal697 := by rfl
theorem left353 : leftChild 9 PR SL normal697 1 9 303696 = cell707 := by
  calc
    leftChild 9 PR SL normal697 1 9 303696 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal697) 1 9 303696).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal697) 1 9 303696).symm
    _ = cell707 := by rfl
theorem right353 : rightChild 9 PR SL normal697 1 9 303696 = cell708 := by
  calc
    rightChild 9 PR SL normal697 1 9 303696 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal697) 1 9 303696).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal697) 1 9 303696).symm
    _ = cell708 := by rfl
theorem normalized354 : AdaptiveCoverage.normalize SL cell708 = normal699 := by
  calc
    AdaptiveCoverage.normalize SL cell708 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell708)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell708)).symm
    _ = normal699 := by rfl
theorem left354 : leftChild 9 PR SL normal699 0 9 341264 = cell709 := by
  calc
    leftChild 9 PR SL normal699 0 9 341264 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal699) 0 9 341264).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal699) 0 9 341264).symm
    _ = cell709 := by rfl
theorem right354 : rightChild 9 PR SL normal699 0 9 341264 = cell710 := by
  calc
    rightChild 9 PR SL normal699 0 9 341264 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal699) 0 9 341264).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal699) 0 9 341264).symm
    _ = cell710 := by rfl
theorem normalized355 : AdaptiveCoverage.normalize SL cell702 = normal703 := by
  calc
    AdaptiveCoverage.normalize SL cell702 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell702)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell702)).symm
    _ = normal703 := by rfl
theorem left355 : leftChild 9 PR SL normal703 0 6 236832 = cell711 := by
  calc
    leftChild 9 PR SL normal703 0 6 236832 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal703) 0 6 236832).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal703) 0 6 236832).symm
    _ = cell711 := by rfl
theorem right355 : rightChild 9 PR SL normal703 0 6 236832 = cell712 := by
  calc
    rightChild 9 PR SL normal703 0 6 236832 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal703) 0 6 236832).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal703) 0 6 236832).symm
    _ = cell712 := by rfl
theorem normalized356 : AdaptiveCoverage.normalize SL cell712 = normal705 := by
  calc
    AdaptiveCoverage.normalize SL cell712 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell712)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell712)).symm
    _ = normal705 := by rfl
theorem left356 : leftChild 9 PR SL normal705 0 6 248670 = cell713 := by
  calc
    leftChild 9 PR SL normal705 0 6 248670 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal705) 0 6 248670).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal705) 0 6 248670).symm
    _ = cell713 := by rfl
theorem right356 : rightChild 9 PR SL normal705 0 6 248670 = cell714 := by
  calc
    rightChild 9 PR SL normal705 0 6 248670 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal705) 0 6 248670).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal705) 0 6 248670).symm
    _ = cell714 := by rfl
theorem normalized357 : AdaptiveCoverage.normalize SL cell713 = normal706 := by
  calc
    AdaptiveCoverage.normalize SL cell713 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell713)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell713)).symm
    _ = normal706 := by rfl
theorem left357 : leftChild 9 PR SL normal706 1 5 137600 = cell715 := by
  calc
    leftChild 9 PR SL normal706 1 5 137600 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal706) 1 5 137600).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal706) 1 5 137600).symm
    _ = cell715 := by rfl
theorem right357 : rightChild 9 PR SL normal706 1 5 137600 = cell716 := by
  calc
    rightChild 9 PR SL normal706 1 5 137600 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal706) 1 5 137600).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal706) 1 5 137600).symm
    _ = cell716 := by rfl
theorem normalized358 : AdaptiveCoverage.normalize SL cell716 = normal708 := by
  calc
    AdaptiveCoverage.normalize SL cell716 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell716)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell716)).symm
    _ = normal708 := by rfl
theorem left358 : leftChild 9 PR SL normal708 1 8 270992 = cell717 := by
  calc
    leftChild 9 PR SL normal708 1 8 270992 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal708) 1 8 270992).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal708) 1 8 270992).symm
    _ = cell717 := by rfl
theorem right358 : rightChild 9 PR SL normal708 1 8 270992 = cell718 := by
  calc
    rightChild 9 PR SL normal708 1 8 270992 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal708) 1 8 270992).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal708) 1 8 270992).symm
    _ = cell718 := by rfl
theorem normalized359 : AdaptiveCoverage.normalize SL cell718 = normal710 := by
  calc
    AdaptiveCoverage.normalize SL cell718 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell718)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell718)).symm
    _ = normal710 := by rfl
theorem left359 : leftChild 9 PR SL normal710 0 8 306064 = cell719 := by
  calc
    leftChild 9 PR SL normal710 0 8 306064 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal710) 0 8 306064).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal710) 0 8 306064).symm
    _ = cell719 := by rfl
theorem right359 : rightChild 9 PR SL normal710 0 8 306064 = cell720 := by
  calc
    rightChild 9 PR SL normal710 0 8 306064 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal710) 0 8 306064).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal710) 0 8 306064).symm
    _ = cell720 := by rfl

set_option pp.fullNames true
#print axioms normalized352
#print axioms left352
#print axioms right352
#print axioms normalized353
#print axioms left353
#print axioms right353
#print axioms normalized354
#print axioms left354
#print axioms right354
#print axioms normalized355
#print axioms left355
#print axioms right355
#print axioms normalized356
#print axioms left356
#print axioms right356
#print axioms normalized357
#print axioms left357
#print axioms right357
#print axioms normalized358
#print axioms left358
#print axioms right358
#print axioms normalized359
#print axioms left359
#print axioms right359
end StructuralGoal20261016.W10Aux478
end
