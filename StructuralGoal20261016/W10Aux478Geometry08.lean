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
theorem normalized064 : AdaptiveCoverage.normalize SL cell127 = normal113 := by
  calc
    AdaptiveCoverage.normalize SL cell127 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell127)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell127)).symm
    _ = normal113 := by rfl
theorem left064 : leftChild 9 PR SL normal113 2 5 98304 = cell129 := by
  calc
    leftChild 9 PR SL normal113 2 5 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal113) 2 5 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal113) 2 5 98304).symm
    _ = cell129 := by rfl
theorem right064 : rightChild 9 PR SL normal113 2 5 98304 = cell130 := by
  calc
    rightChild 9 PR SL normal113 2 5 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal113) 2 5 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal113) 2 5 98304).symm
    _ = cell130 := by rfl
theorem normalized065 : AdaptiveCoverage.normalize SL cell130 = normal115 := by
  calc
    AdaptiveCoverage.normalize SL cell130 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell130)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell130)).symm
    _ = normal115 := by rfl
theorem left065 : leftChild 9 PR SL normal115 2 4 81920 = cell131 := by
  calc
    leftChild 9 PR SL normal115 2 4 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal115) 2 4 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal115) 2 4 81920).symm
    _ = cell131 := by rfl
theorem right065 : rightChild 9 PR SL normal115 2 4 81920 = cell132 := by
  calc
    rightChild 9 PR SL normal115 2 4 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal115) 2 4 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal115) 2 4 81920).symm
    _ = cell132 := by rfl
theorem normalized066 : AdaptiveCoverage.normalize SL cell131 = normal116 := by
  calc
    AdaptiveCoverage.normalize SL cell131 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell131)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell131)).symm
    _ = normal116 := by rfl
theorem left066 : leftChild 9 PR SL normal116 2 9 262144 = cell133 := by
  calc
    leftChild 9 PR SL normal116 2 9 262144 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal116) 2 9 262144).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal116) 2 9 262144).symm
    _ = cell133 := by rfl
theorem right066 : rightChild 9 PR SL normal116 2 9 262144 = cell134 := by
  calc
    rightChild 9 PR SL normal116 2 9 262144 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal116) 2 9 262144).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal116) 2 9 262144).symm
    _ = cell134 := by rfl
theorem normalized067 : AdaptiveCoverage.normalize SL cell133 = normal117 := by
  calc
    AdaptiveCoverage.normalize SL cell133 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell133)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell133)).symm
    _ = normal117 := by rfl
theorem left067 : leftChild 9 PR SL normal117 4 7 98304 = cell135 := by
  calc
    leftChild 9 PR SL normal117 4 7 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal117) 4 7 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal117) 4 7 98304).symm
    _ = cell135 := by rfl
theorem right067 : rightChild 9 PR SL normal117 4 7 98304 = cell136 := by
  calc
    rightChild 9 PR SL normal117 4 7 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal117) 4 7 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal117) 4 7 98304).symm
    _ = cell136 := by rfl
theorem normalized068 : AdaptiveCoverage.normalize SL cell136 = normal119 := by
  calc
    AdaptiveCoverage.normalize SL cell136 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell136)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell136)).symm
    _ = normal119 := by rfl
theorem left068 : leftChild 9 PR SL normal119 3 8 180224 = cell137 := by
  calc
    leftChild 9 PR SL normal119 3 8 180224 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal119) 3 8 180224).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal119) 3 8 180224).symm
    _ = cell137 := by rfl
theorem right068 : rightChild 9 PR SL normal119 3 8 180224 = cell138 := by
  calc
    rightChild 9 PR SL normal119 3 8 180224 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal119) 3 8 180224).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal119) 3 8 180224).symm
    _ = cell138 := by rfl
theorem normalized069 : AdaptiveCoverage.normalize SL cell134 = normal122 := by
  calc
    AdaptiveCoverage.normalize SL cell134 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell134)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell134)).symm
    _ = normal122 := by rfl
theorem left069 : leftChild 9 PR SL normal122 4 7 98304 = cell139 := by
  calc
    leftChild 9 PR SL normal122 4 7 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal122) 4 7 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal122) 4 7 98304).symm
    _ = cell139 := by rfl
theorem right069 : rightChild 9 PR SL normal122 4 7 98304 = cell140 := by
  calc
    rightChild 9 PR SL normal122 4 7 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal122) 4 7 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal122) 4 7 98304).symm
    _ = cell140 := by rfl
theorem normalized070 : AdaptiveCoverage.normalize SL cell140 = normal124 := by
  calc
    AdaptiveCoverage.normalize SL cell140 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell140)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell140)).symm
    _ = normal124 := by rfl
theorem left070 : leftChild 9 PR SL normal124 2 6 147456 = cell141 := by
  calc
    leftChild 9 PR SL normal124 2 6 147456 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal124) 2 6 147456).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal124) 2 6 147456).symm
    _ = cell141 := by rfl
theorem right070 : rightChild 9 PR SL normal124 2 6 147456 = cell142 := by
  calc
    rightChild 9 PR SL normal124 2 6 147456 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal124) 2 6 147456).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal124) 2 6 147456).symm
    _ = cell142 := by rfl
theorem normalized071 : AdaptiveCoverage.normalize SL cell141 = normal125 := by
  calc
    AdaptiveCoverage.normalize SL cell141 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell141)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell141)).symm
    _ = normal125 := by rfl
theorem left071 : leftChild 9 PR SL normal125 3 8 180224 = cell143 := by
  calc
    leftChild 9 PR SL normal125 3 8 180224 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal125) 3 8 180224).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal125) 3 8 180224).symm
    _ = cell143 := by rfl
theorem right071 : rightChild 9 PR SL normal125 3 8 180224 = cell144 := by
  calc
    rightChild 9 PR SL normal125 3 8 180224 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal125) 3 8 180224).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal125) 3 8 180224).symm
    _ = cell144 := by rfl

set_option pp.fullNames true
#print axioms normalized064
#print axioms left064
#print axioms right064
#print axioms normalized065
#print axioms left065
#print axioms right065
#print axioms normalized066
#print axioms left066
#print axioms right066
#print axioms normalized067
#print axioms left067
#print axioms right067
#print axioms normalized068
#print axioms left068
#print axioms right068
#print axioms normalized069
#print axioms left069
#print axioms right069
#print axioms normalized070
#print axioms left070
#print axioms right070
#print axioms normalized071
#print axioms left071
#print axioms right071
end StructuralGoal20261016.W10Aux478
end
