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
theorem normalized336 : AdaptiveCoverage.normalize SL cell671 = normal665 := by
  calc
    AdaptiveCoverage.normalize SL cell671 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell671)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell671)).symm
    _ = normal665 := by rfl
theorem left336 : leftChild 9 PR SL normal665 0 6 203088 = cell673 := by
  calc
    leftChild 9 PR SL normal665 0 6 203088 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal665) 0 6 203088).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal665) 0 6 203088).symm
    _ = cell673 := by rfl
theorem right336 : rightChild 9 PR SL normal665 0 6 203088 = cell674 := by
  calc
    rightChild 9 PR SL normal665 0 6 203088 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal665) 0 6 203088).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal665) 0 6 203088).symm
    _ = cell674 := by rfl
theorem normalized337 : AdaptiveCoverage.normalize SL cell672 = normal668 := by
  calc
    AdaptiveCoverage.normalize SL cell672 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell672)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell672)).symm
    _ = normal668 := by rfl
theorem left337 : leftChild 9 PR SL normal668 0 6 206240 = cell675 := by
  calc
    leftChild 9 PR SL normal668 0 6 206240 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal668) 0 6 206240).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal668) 0 6 206240).symm
    _ = cell675 := by rfl
theorem right337 : rightChild 9 PR SL normal668 0 6 206240 = cell676 := by
  calc
    rightChild 9 PR SL normal668 0 6 206240 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal668) 0 6 206240).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal668) 0 6 206240).symm
    _ = cell676 := by rfl
theorem normalized338 : AdaptiveCoverage.normalize SL cell072 = normal671 := by
  calc
    AdaptiveCoverage.normalize SL cell072 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell072)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell072)).symm
    _ = normal671 := by rfl
theorem left338 : leftChild 9 PR SL normal671 2 3 59281 = cell677 := by
  calc
    leftChild 9 PR SL normal671 2 3 59281 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal671) 2 3 59281).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal671) 2 3 59281).symm
    _ = cell677 := by rfl
theorem right338 : rightChild 9 PR SL normal671 2 3 59281 = cell678 := by
  calc
    rightChild 9 PR SL normal671 2 3 59281 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal671) 2 3 59281).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal671) 2 3 59281).symm
    _ = cell678 := by rfl
theorem normalized339 : AdaptiveCoverage.normalize SL cell677 = normal672 := by
  calc
    AdaptiveCoverage.normalize SL cell677 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell677)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell677)).symm
    _ = normal672 := by rfl
theorem left339 : leftChild 9 PR SL normal672 3 4 59270 = cell679 := by
  calc
    leftChild 9 PR SL normal672 3 4 59270 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal672) 3 4 59270).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal672) 3 4 59270).symm
    _ = cell679 := by rfl
theorem right339 : rightChild 9 PR SL normal672 3 4 59270 = cell680 := by
  calc
    rightChild 9 PR SL normal672 3 4 59270 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal672) 3 4 59270).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal672) 3 4 59270).symm
    _ = cell680 := by rfl
theorem normalized340 : AdaptiveCoverage.normalize SL cell679 = normal673 := by
  calc
    AdaptiveCoverage.normalize SL cell679 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell679)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell679)).symm
    _ = normal673 := by rfl
theorem left340 : leftChild 9 PR SL normal673 5 6 59238 = cell681 := by
  calc
    leftChild 9 PR SL normal673 5 6 59238 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal673) 5 6 59238).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal673) 5 6 59238).symm
    _ = cell681 := by rfl
theorem right340 : rightChild 9 PR SL normal673 5 6 59238 = cell682 := by
  calc
    rightChild 9 PR SL normal673 5 6 59238 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal673) 5 6 59238).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal673) 5 6 59238).symm
    _ = cell682 := by rfl
theorem normalized341 : AdaptiveCoverage.normalize SL cell681 = normal674 := by
  calc
    AdaptiveCoverage.normalize SL cell681 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell681)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell681)).symm
    _ = normal674 := by rfl
theorem left341 : leftChild 9 PR SL normal674 4 5 59211 = cell683 := by
  calc
    leftChild 9 PR SL normal674 4 5 59211 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal674) 4 5 59211).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal674) 4 5 59211).symm
    _ = cell683 := by rfl
theorem right341 : rightChild 9 PR SL normal674 4 5 59211 = cell684 := by
  calc
    rightChild 9 PR SL normal674 4 5 59211 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal674) 4 5 59211).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal674) 4 5 59211).symm
    _ = cell684 := by rfl
theorem normalized342 : AdaptiveCoverage.normalize SL cell684 = normal676 := by
  calc
    AdaptiveCoverage.normalize SL cell684 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell684)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell684)).symm
    _ = normal676 := by rfl
theorem left342 : leftChild 9 PR SL normal676 1 8 271632 = cell685 := by
  calc
    leftChild 9 PR SL normal676 1 8 271632 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal676) 1 8 271632).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal676) 1 8 271632).symm
    _ = cell685 := by rfl
theorem right342 : rightChild 9 PR SL normal676 1 8 271632 = cell686 := by
  calc
    rightChild 9 PR SL normal676 1 8 271632 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal676) 1 8 271632).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal676) 1 8 271632).symm
    _ = cell686 := by rfl
theorem normalized343 : AdaptiveCoverage.normalize SL cell686 = normal678 := by
  calc
    AdaptiveCoverage.normalize SL cell686 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell686)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell686)).symm
    _ = normal678 := by rfl
theorem left343 : leftChild 9 PR SL normal678 0 8 307264 = cell687 := by
  calc
    leftChild 9 PR SL normal678 0 8 307264 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal678) 0 8 307264).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal678) 0 8 307264).symm
    _ = cell687 := by rfl
theorem right343 : rightChild 9 PR SL normal678 0 8 307264 = cell688 := by
  calc
    rightChild 9 PR SL normal678 0 8 307264 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal678) 0 8 307264).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal678) 0 8 307264).symm
    _ = cell688 := by rfl

set_option pp.fullNames true
#print axioms normalized336
#print axioms left336
#print axioms right336
#print axioms normalized337
#print axioms left337
#print axioms right337
#print axioms normalized338
#print axioms left338
#print axioms right338
#print axioms normalized339
#print axioms left339
#print axioms right339
#print axioms normalized340
#print axioms left340
#print axioms right340
#print axioms normalized341
#print axioms left341
#print axioms right341
#print axioms normalized342
#print axioms left342
#print axioms right342
#print axioms normalized343
#print axioms left343
#print axioms right343
end StructuralGoal20261016.W10Aux478
end
