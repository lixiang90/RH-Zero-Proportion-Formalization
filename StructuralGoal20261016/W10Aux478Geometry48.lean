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
theorem normalized384 : AdaptiveCoverage.normalize SL cell767 = normal755 := by
  calc
    AdaptiveCoverage.normalize SL cell767 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell767)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell767)).symm
    _ = normal755 := by rfl
theorem left384 : leftChild 9 PR SL normal755 1 8 242305 = cell769 := by
  calc
    leftChild 9 PR SL normal755 1 8 242305 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal755) 1 8 242305).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal755) 1 8 242305).symm
    _ = cell769 := by rfl
theorem right384 : rightChild 9 PR SL normal755 1 8 242305 = cell770 := by
  calc
    rightChild 9 PR SL normal755 1 8 242305 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal755) 1 8 242305).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal755) 1 8 242305).symm
    _ = cell770 := by rfl
theorem normalized385 : AdaptiveCoverage.normalize SL cell768 = normal758 := by
  calc
    AdaptiveCoverage.normalize SL cell768 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell768)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell768)).symm
    _ = normal758 := by rfl
theorem left385 : leftChild 9 PR SL normal758 3 7 140928 = cell771 := by
  calc
    leftChild 9 PR SL normal758 3 7 140928 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal758) 3 7 140928).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal758) 3 7 140928).symm
    _ = cell771 := by rfl
theorem right385 : rightChild 9 PR SL normal758 3 7 140928 = cell772 := by
  calc
    rightChild 9 PR SL normal758 3 7 140928 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal758) 3 7 140928).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal758) 3 7 140928).symm
    _ = cell772 := by rfl
theorem normalized386 : AdaptiveCoverage.normalize SL cell766 = normal761 := by
  calc
    AdaptiveCoverage.normalize SL cell766 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell766)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell766)).symm
    _ = normal761 := by rfl
theorem left386 : leftChild 9 PR SL normal761 8 9 49131 = cell773 := by
  calc
    leftChild 9 PR SL normal761 8 9 49131 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal761) 8 9 49131).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal761) 8 9 49131).symm
    _ = cell773 := by rfl
theorem right386 : rightChild 9 PR SL normal761 8 9 49131 = cell774 := by
  calc
    rightChild 9 PR SL normal761 8 9 49131 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal761) 8 9 49131).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal761) 8 9 49131).symm
    _ = cell774 := by rfl
theorem normalized387 : AdaptiveCoverage.normalize SL cell773 = normal762 := by
  calc
    AdaptiveCoverage.normalize SL cell773 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell773)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell773)).symm
    _ = normal762 := by rfl
theorem left387 : leftChild 9 PR SL normal762 4 5 80028 = cell775 := by
  calc
    leftChild 9 PR SL normal762 4 5 80028 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal762) 4 5 80028).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal762) 4 5 80028).symm
    _ = cell775 := by rfl
theorem right387 : rightChild 9 PR SL normal762 4 5 80028 = cell776 := by
  calc
    rightChild 9 PR SL normal762 4 5 80028 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal762) 4 5 80028).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal762) 4 5 80028).symm
    _ = cell776 := by rfl
theorem normalized388 : AdaptiveCoverage.normalize SL cell775 = normal763 := by
  calc
    AdaptiveCoverage.normalize SL cell775 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell775)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell775)).symm
    _ = normal763 := by rfl
theorem left388 : leftChild 9 PR SL normal763 2 6 173168 = cell777 := by
  calc
    leftChild 9 PR SL normal763 2 6 173168 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal763) 2 6 173168).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal763) 2 6 173168).symm
    _ = cell777 := by rfl
theorem right388 : rightChild 9 PR SL normal763 2 6 173168 = cell778 := by
  calc
    rightChild 9 PR SL normal763 2 6 173168 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal763) 2 6 173168).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal763) 2 6 173168).symm
    _ = cell778 := by rfl
theorem normalized389 : AdaptiveCoverage.normalize SL cell777 = normal764 := by
  calc
    AdaptiveCoverage.normalize SL cell777 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell777)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell777)).symm
    _ = normal764 := by rfl
theorem left389 : leftChild 9 PR SL normal764 0 8 309872 = cell779 := by
  calc
    leftChild 9 PR SL normal764 0 8 309872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal764) 0 8 309872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal764) 0 8 309872).symm
    _ = cell779 := by rfl
theorem right389 : rightChild 9 PR SL normal764 0 8 309872 = cell780 := by
  calc
    rightChild 9 PR SL normal764 0 8 309872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal764) 0 8 309872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal764) 0 8 309872).symm
    _ = cell780 := by rfl
theorem normalized390 : AdaptiveCoverage.normalize SL cell780 = normal766 := by
  calc
    AdaptiveCoverage.normalize SL cell780 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell780)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell780)).symm
    _ = normal766 := by rfl
theorem left390 : leftChild 9 PR SL normal766 1 9 310847 = cell781 := by
  calc
    leftChild 9 PR SL normal766 1 9 310847 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal766) 1 9 310847).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal766) 1 9 310847).symm
    _ = cell781 := by rfl
theorem right390 : rightChild 9 PR SL normal766 1 9 310847 = cell782 := by
  calc
    rightChild 9 PR SL normal766 1 9 310847 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal766) 1 9 310847).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal766) 1 9 310847).symm
    _ = cell782 := by rfl
theorem normalized391 : AdaptiveCoverage.normalize SL cell778 = normal769 := by
  calc
    AdaptiveCoverage.normalize SL cell778 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell778)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell778)).symm
    _ = normal769 := by rfl
theorem left391 : leftChild 9 PR SL normal769 3 7 173935 = cell783 := by
  calc
    leftChild 9 PR SL normal769 3 7 173935 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal769) 3 7 173935).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal769) 3 7 173935).symm
    _ = cell783 := by rfl
theorem right391 : rightChild 9 PR SL normal769 3 7 173935 = cell784 := by
  calc
    rightChild 9 PR SL normal769 3 7 173935 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal769) 3 7 173935).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal769) 3 7 173935).symm
    _ = cell784 := by rfl

set_option pp.fullNames true
#print axioms normalized384
#print axioms left384
#print axioms right384
#print axioms normalized385
#print axioms left385
#print axioms right385
#print axioms normalized386
#print axioms left386
#print axioms right386
#print axioms normalized387
#print axioms left387
#print axioms right387
#print axioms normalized388
#print axioms left388
#print axioms right388
#print axioms normalized389
#print axioms left389
#print axioms right389
#print axioms normalized390
#print axioms left390
#print axioms right390
#print axioms normalized391
#print axioms left391
#print axioms right391
end StructuralGoal20261016.W10Aux478
end
