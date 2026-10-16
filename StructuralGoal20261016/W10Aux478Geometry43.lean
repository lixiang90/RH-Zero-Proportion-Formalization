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
theorem normalized344 : AdaptiveCoverage.normalize SL cell687 = normal679 := by
  calc
    AdaptiveCoverage.normalize SL cell687 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell687)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell687)).symm
    _ = normal679 := by rfl
theorem left344 : leftChild 9 PR SL normal679 1 9 305696 = cell689 := by
  calc
    leftChild 9 PR SL normal679 1 9 305696 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal679) 1 9 305696).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal679) 1 9 305696).symm
    _ = cell689 := by rfl
theorem right344 : rightChild 9 PR SL normal679 1 9 305696 = cell690 := by
  calc
    rightChild 9 PR SL normal679 1 9 305696 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal679) 1 9 305696).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal679) 1 9 305696).symm
    _ = cell690 := by rfl
theorem normalized345 : AdaptiveCoverage.normalize SL cell690 = normal681 := by
  calc
    AdaptiveCoverage.normalize SL cell690 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell690)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell690)).symm
    _ = normal681 := by rfl
theorem left345 : leftChild 9 PR SL normal681 0 9 342064 = cell691 := by
  calc
    leftChild 9 PR SL normal681 0 9 342064 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal681) 0 9 342064).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal681) 0 9 342064).symm
    _ = cell691 := by rfl
theorem right345 : rightChild 9 PR SL normal681 0 9 342064 = cell692 := by
  calc
    rightChild 9 PR SL normal681 0 9 342064 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal681) 0 9 342064).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal681) 0 9 342064).symm
    _ = cell692 := by rfl
theorem normalized346 : AdaptiveCoverage.normalize SL cell691 = normal682 := by
  calc
    AdaptiveCoverage.normalize SL cell691 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell691)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell691)).symm
    _ = normal682 := by rfl
theorem left346 : leftChild 9 PR SL normal682 0 9 337806 = cell693 := by
  calc
    leftChild 9 PR SL normal682 0 9 337806 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal682) 0 9 337806).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal682) 0 9 337806).symm
    _ = cell693 := by rfl
theorem right346 : rightChild 9 PR SL normal682 0 9 337806 = cell694 := by
  calc
    rightChild 9 PR SL normal682 0 9 337806 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal682) 0 9 337806).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal682) 0 9 337806).symm
    _ = cell694 := by rfl
theorem normalized347 : AdaptiveCoverage.normalize SL cell688 = normal686 := by
  calc
    AdaptiveCoverage.normalize SL cell688 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell688)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell688)).symm
    _ = normal686 := by rfl
theorem left347 : leftChild 9 PR SL normal686 0 9 339590 = cell695 := by
  calc
    leftChild 9 PR SL normal686 0 9 339590 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal686) 0 9 339590).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal686) 0 9 339590).symm
    _ = cell695 := by rfl
theorem right347 : rightChild 9 PR SL normal686 0 9 339590 = cell696 := by
  calc
    rightChild 9 PR SL normal686 0 9 339590 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal686) 0 9 339590).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal686) 0 9 339590).symm
    _ = cell696 := by rfl
theorem normalized348 : AdaptiveCoverage.normalize SL cell696 = normal688 := by
  calc
    AdaptiveCoverage.normalize SL cell696 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell696)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell696)).symm
    _ = normal688 := by rfl
theorem left348 : leftChild 9 PR SL normal688 1 9 309520 = cell697 := by
  calc
    leftChild 9 PR SL normal688 1 9 309520 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal688) 1 9 309520).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal688) 1 9 309520).symm
    _ = cell697 := by rfl
theorem right348 : rightChild 9 PR SL normal688 1 9 309520 = cell698 := by
  calc
    rightChild 9 PR SL normal688 1 9 309520 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal688) 1 9 309520).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal688) 1 9 309520).symm
    _ = cell698 := by rfl
theorem normalized349 : AdaptiveCoverage.normalize SL cell698 = normal690 := by
  calc
    AdaptiveCoverage.normalize SL cell698 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell698)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell698)).symm
    _ = normal690 := by rfl
theorem left349 : leftChild 9 PR SL normal690 0 6 240080 = cell699 := by
  calc
    leftChild 9 PR SL normal690 0 6 240080 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal690) 0 6 240080).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal690) 0 6 240080).symm
    _ = cell699 := by rfl
theorem right349 : rightChild 9 PR SL normal690 0 6 240080 = cell700 := by
  calc
    rightChild 9 PR SL normal690 0 6 240080 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal690) 0 6 240080).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal690) 0 6 240080).symm
    _ = cell700 := by rfl
theorem normalized350 : AdaptiveCoverage.normalize SL cell682 = normal693 := by
  calc
    AdaptiveCoverage.normalize SL cell682 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell682)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell682)).symm
    _ = normal693 := by rfl
theorem left350 : leftChild 9 PR SL normal693 2 5 103376 = cell701 := by
  calc
    leftChild 9 PR SL normal693 2 5 103376 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal693) 2 5 103376).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal693) 2 5 103376).symm
    _ = cell701 := by rfl
theorem right350 : rightChild 9 PR SL normal693 2 5 103376 = cell702 := by
  calc
    rightChild 9 PR SL normal693 2 5 103376 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal693) 2 5 103376).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal693) 2 5 103376).symm
    _ = cell702 := by rfl
theorem normalized351 : AdaptiveCoverage.normalize SL cell701 = normal694 := by
  calc
    AdaptiveCoverage.normalize SL cell701 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell701)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell701)).symm
    _ = normal694 := by rfl
theorem left351 : leftChild 9 PR SL normal694 3 9 235824 = cell703 := by
  calc
    leftChild 9 PR SL normal694 3 9 235824 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal694) 3 9 235824).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal694) 3 9 235824).symm
    _ = cell703 := by rfl
theorem right351 : rightChild 9 PR SL normal694 3 9 235824 = cell704 := by
  calc
    rightChild 9 PR SL normal694 3 9 235824 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal694) 3 9 235824).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal694) 3 9 235824).symm
    _ = cell704 := by rfl

set_option pp.fullNames true
#print axioms normalized344
#print axioms left344
#print axioms right344
#print axioms normalized345
#print axioms left345
#print axioms right345
#print axioms normalized346
#print axioms left346
#print axioms right346
#print axioms normalized347
#print axioms left347
#print axioms right347
#print axioms normalized348
#print axioms left348
#print axioms right348
#print axioms normalized349
#print axioms left349
#print axioms right349
#print axioms normalized350
#print axioms left350
#print axioms right350
#print axioms normalized351
#print axioms left351
#print axioms right351
end StructuralGoal20261016.W10Aux478
end
