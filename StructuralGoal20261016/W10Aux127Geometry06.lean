/- Frozen 127-leaf W10 subtree; complete global coverage is not asserted. -/
import StructuralGoal20261016.W10Aux127Data
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
namespace StructuralGoal20261016.W10Aux127
theorem normalized048 : AdaptiveCoverage.normalize SL cell096 = normal088 := by
  calc
    AdaptiveCoverage.normalize SL cell096 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell096)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell096)).symm
    _ = normal088 := by rfl
theorem left048 : leftChild 9 PR SL normal088 3 5 65536 = cell097 := by
  calc
    leftChild 9 PR SL normal088 3 5 65536 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal088) 3 5 65536).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal088) 3 5 65536).symm
    _ = cell097 := by rfl
theorem right048 : rightChild 9 PR SL normal088 3 5 65536 = cell098 := by
  calc
    rightChild 9 PR SL normal088 3 5 65536 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal088) 3 5 65536).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal088) 3 5 65536).symm
    _ = cell098 := by rfl
theorem normalized049 : AdaptiveCoverage.normalize SL cell098 = normal090 := by
  calc
    AdaptiveCoverage.normalize SL cell098 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell098)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell098)).symm
    _ = normal090 := by rfl
theorem left049 : leftChild 9 PR SL normal090 4 6 65536 = cell099 := by
  calc
    leftChild 9 PR SL normal090 4 6 65536 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal090) 4 6 65536).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal090) 4 6 65536).symm
    _ = cell099 := by rfl
theorem right049 : rightChild 9 PR SL normal090 4 6 65536 = cell100 := by
  calc
    rightChild 9 PR SL normal090 4 6 65536 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal090) 4 6 65536).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal090) 4 6 65536).symm
    _ = cell100 := by rfl
theorem normalized050 : AdaptiveCoverage.normalize SL cell100 = normal092 := by
  calc
    AdaptiveCoverage.normalize SL cell100 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell100)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell100)).symm
    _ = normal092 := by rfl
theorem left050 : leftChild 9 PR SL normal092 3 9 229376 = cell101 := by
  calc
    leftChild 9 PR SL normal092 3 9 229376 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal092) 3 9 229376).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal092) 3 9 229376).symm
    _ = cell101 := by rfl
theorem right050 : rightChild 9 PR SL normal092 3 9 229376 = cell102 := by
  calc
    rightChild 9 PR SL normal092 3 9 229376 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal092) 3 9 229376).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal092) 3 9 229376).symm
    _ = cell102 := by rfl
theorem normalized051 : AdaptiveCoverage.normalize SL cell101 = normal093 := by
  calc
    AdaptiveCoverage.normalize SL cell101 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell101)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell101)).symm
    _ = normal093 := by rfl
theorem left051 : leftChild 9 PR SL normal093 5 7 81920 = cell103 := by
  calc
    leftChild 9 PR SL normal093 5 7 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal093) 5 7 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal093) 5 7 81920).symm
    _ = cell103 := by rfl
theorem right051 : rightChild 9 PR SL normal093 5 7 81920 = cell104 := by
  calc
    rightChild 9 PR SL normal093 5 7 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal093) 5 7 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal093) 5 7 81920).symm
    _ = cell104 := by rfl
theorem normalized052 : AdaptiveCoverage.normalize SL cell014 = normal100 := by
  calc
    AdaptiveCoverage.normalize SL cell014 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell014)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell014)).symm
    _ = normal100 := by rfl
theorem left052 : leftChild 9 PR SL normal100 3 7 147456 = cell105 := by
  calc
    leftChild 9 PR SL normal100 3 7 147456 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal100) 3 7 147456).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal100) 3 7 147456).symm
    _ = cell105 := by rfl
theorem right052 : rightChild 9 PR SL normal100 3 7 147456 = cell106 := by
  calc
    rightChild 9 PR SL normal100 3 7 147456 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal100) 3 7 147456).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal100) 3 7 147456).symm
    _ = cell106 := by rfl
theorem normalized053 : AdaptiveCoverage.normalize SL cell105 = normal101 := by
  calc
    AdaptiveCoverage.normalize SL cell105 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell105)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell105)).symm
    _ = normal101 := by rfl
theorem left053 : leftChild 9 PR SL normal101 3 9 212992 = cell107 := by
  calc
    leftChild 9 PR SL normal101 3 9 212992 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal101) 3 9 212992).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal101) 3 9 212992).symm
    _ = cell107 := by rfl
theorem right053 : rightChild 9 PR SL normal101 3 9 212992 = cell108 := by
  calc
    rightChild 9 PR SL normal101 3 9 212992 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal101) 3 9 212992).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal101) 3 9 212992).symm
    _ = cell108 := by rfl
theorem normalized054 : AdaptiveCoverage.normalize SL cell107 = normal102 := by
  calc
    AdaptiveCoverage.normalize SL cell107 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell107)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell107)).symm
    _ = normal102 := by rfl
theorem left054 : leftChild 9 PR SL normal102 2 5 114688 = cell109 := by
  calc
    leftChild 9 PR SL normal102 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal102) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal102) 2 5 114688).symm
    _ = cell109 := by rfl
theorem right054 : rightChild 9 PR SL normal102 2 5 114688 = cell110 := by
  calc
    rightChild 9 PR SL normal102 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal102) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal102) 2 5 114688).symm
    _ = cell110 := by rfl
theorem normalized055 : AdaptiveCoverage.normalize SL cell110 = normal104 := by
  calc
    AdaptiveCoverage.normalize SL cell110 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell110)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell110)).symm
    _ = normal104 := by rfl
theorem left055 : leftChild 9 PR SL normal104 2 4 98304 = cell111 := by
  calc
    leftChild 9 PR SL normal104 2 4 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal104) 2 4 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal104) 2 4 98304).symm
    _ = cell111 := by rfl
theorem right055 : rightChild 9 PR SL normal104 2 4 98304 = cell112 := by
  calc
    rightChild 9 PR SL normal104 2 4 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal104) 2 4 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal104) 2 4 98304).symm
    _ = cell112 := by rfl

set_option pp.fullNames true
#print axioms normalized048
#print axioms left048
#print axioms right048
#print axioms normalized049
#print axioms left049
#print axioms right049
#print axioms normalized050
#print axioms left050
#print axioms right050
#print axioms normalized051
#print axioms left051
#print axioms right051
#print axioms normalized052
#print axioms left052
#print axioms right052
#print axioms normalized053
#print axioms left053
#print axioms right053
#print axioms normalized054
#print axioms left054
#print axioms right054
#print axioms normalized055
#print axioms left055
#print axioms right055
end StructuralGoal20261016.W10Aux127
end
