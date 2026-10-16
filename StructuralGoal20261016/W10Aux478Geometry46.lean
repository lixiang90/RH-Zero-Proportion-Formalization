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
theorem normalized368 : AdaptiveCoverage.normalize SL cell735 = normal729 := by
  calc
    AdaptiveCoverage.normalize SL cell735 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell735)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell735)).symm
    _ = normal729 := by rfl
theorem left368 : leftChild 9 PR SL normal729 4 8 137600 = cell737 := by
  calc
    leftChild 9 PR SL normal729 4 8 137600 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal729) 4 8 137600).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal729) 4 8 137600).symm
    _ = cell737 := by rfl
theorem right368 : rightChild 9 PR SL normal729 4 8 137600 = cell738 := by
  calc
    rightChild 9 PR SL normal729 4 8 137600 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal729) 4 8 137600).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal729) 4 8 137600).symm
    _ = cell738 := by rfl
theorem normalized369 : AdaptiveCoverage.normalize SL cell738 = normal731 := by
  calc
    AdaptiveCoverage.normalize SL cell738 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell738)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell738)).symm
    _ = normal731 := by rfl
theorem left369 : leftChild 9 PR SL normal731 1 8 270992 = cell739 := by
  calc
    leftChild 9 PR SL normal731 1 8 270992 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal731) 1 8 270992).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal731) 1 8 270992).symm
    _ = cell739 := by rfl
theorem right369 : rightChild 9 PR SL normal731 1 8 270992 = cell740 := by
  calc
    rightChild 9 PR SL normal731 1 8 270992 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal731) 1 8 270992).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal731) 1 8 270992).symm
    _ = cell740 := by rfl
theorem normalized370 : AdaptiveCoverage.normalize SL cell740 = normal733 := by
  calc
    AdaptiveCoverage.normalize SL cell740 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell740)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell740)).symm
    _ = normal733 := by rfl
theorem left370 : leftChild 9 PR SL normal733 1 9 306080 = cell741 := by
  calc
    leftChild 9 PR SL normal733 1 9 306080 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal733) 1 9 306080).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal733) 1 9 306080).symm
    _ = cell741 := by rfl
theorem right370 : rightChild 9 PR SL normal733 1 9 306080 = cell742 := by
  calc
    rightChild 9 PR SL normal733 1 9 306080 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal733) 1 9 306080).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal733) 1 9 306080).symm
    _ = cell742 := by rfl
theorem normalized371 : AdaptiveCoverage.normalize SL cell742 = normal735 := by
  calc
    AdaptiveCoverage.normalize SL cell742 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell742)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell742)).symm
    _ = normal735 := by rfl
theorem left371 : leftChild 9 PR SL normal735 0 9 338998 = cell743 := by
  calc
    leftChild 9 PR SL normal735 0 9 338998 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal735) 0 9 338998).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal735) 0 9 338998).symm
    _ = cell743 := by rfl
theorem right371 : rightChild 9 PR SL normal735 0 9 338998 = cell744 := by
  calc
    rightChild 9 PR SL normal735 0 9 338998 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal735) 0 9 338998).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal735) 0 9 338998).symm
    _ = cell744 := by rfl
theorem normalized372 : AdaptiveCoverage.normalize SL cell678 = normal739 := by
  calc
    AdaptiveCoverage.normalize SL cell678 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell678)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell678)).symm
    _ = normal739 := by rfl
theorem left372 : leftChild 9 PR SL normal739 3 7 137856 = cell745 := by
  calc
    leftChild 9 PR SL normal739 3 7 137856 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal739) 3 7 137856).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal739) 3 7 137856).symm
    _ = cell745 := by rfl
theorem right372 : rightChild 9 PR SL normal739 3 7 137856 = cell746 := by
  calc
    rightChild 9 PR SL normal739 3 7 137856 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal739) 3 7 137856).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal739) 3 7 137856).symm
    _ = cell746 := by rfl
theorem normalized373 : AdaptiveCoverage.normalize SL cell745 = normal740 := by
  calc
    AdaptiveCoverage.normalize SL cell745 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell745)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell745)).symm
    _ = normal740 := by rfl
theorem left373 : leftChild 9 PR SL normal740 3 9 203088 = cell747 := by
  calc
    leftChild 9 PR SL normal740 3 9 203088 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal740) 3 9 203088).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal740) 3 9 203088).symm
    _ = cell747 := by rfl
theorem right373 : rightChild 9 PR SL normal740 3 9 203088 = cell748 := by
  calc
    rightChild 9 PR SL normal740 3 9 203088 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal740) 3 9 203088).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal740) 3 9 203088).symm
    _ = cell748 := by rfl
theorem normalized374 : AdaptiveCoverage.normalize SL cell746 = normal743 := by
  calc
    AdaptiveCoverage.normalize SL cell746 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell746)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell746)).symm
    _ = normal743 := by rfl
theorem left374 : leftChild 9 PR SL normal743 3 9 206240 = cell749 := by
  calc
    leftChild 9 PR SL normal743 3 9 206240 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal743) 3 9 206240).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal743) 3 9 206240).symm
    _ = cell749 := by rfl
theorem right374 : rightChild 9 PR SL normal743 3 9 206240 = cell750 := by
  calc
    rightChild 9 PR SL normal743 3 9 206240 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal743) 3 9 206240).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal743) 3 9 206240).symm
    _ = cell750 := by rfl
theorem normalized375 : AdaptiveCoverage.normalize SL cell070 = normal746 := by
  calc
    AdaptiveCoverage.normalize SL cell070 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell070)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell070)).symm
    _ = normal746 := by rfl
theorem left375 : leftChild 9 PR SL normal746 0 1 49998 = cell751 := by
  calc
    leftChild 9 PR SL normal746 0 1 49998 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal746) 0 1 49998).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal746) 0 1 49998).symm
    _ = cell751 := by rfl
theorem right375 : rightChild 9 PR SL normal746 0 1 49998 = cell752 := by
  calc
    rightChild 9 PR SL normal746 0 1 49998 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal746) 0 1 49998).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal746) 0 1 49998).symm
    _ = cell752 := by rfl

set_option pp.fullNames true
#print axioms normalized368
#print axioms left368
#print axioms right368
#print axioms normalized369
#print axioms left369
#print axioms right369
#print axioms normalized370
#print axioms left370
#print axioms right370
#print axioms normalized371
#print axioms left371
#print axioms right371
#print axioms normalized372
#print axioms left372
#print axioms right372
#print axioms normalized373
#print axioms left373
#print axioms right373
#print axioms normalized374
#print axioms left374
#print axioms right374
#print axioms normalized375
#print axioms left375
#print axioms right375
end StructuralGoal20261016.W10Aux478
end
