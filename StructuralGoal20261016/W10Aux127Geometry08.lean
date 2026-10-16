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
theorem normalized064 : AdaptiveCoverage.normalize SL cell128 = normal120 := by
  calc
    AdaptiveCoverage.normalize SL cell128 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell128)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell128)).symm
    _ = normal120 := by rfl
theorem left064 : leftChild 9 PR SL normal120 4 6 65536 = cell129 := by
  calc
    leftChild 9 PR SL normal120 4 6 65536 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal120) 4 6 65536).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal120) 4 6 65536).symm
    _ = cell129 := by rfl
theorem right064 : rightChild 9 PR SL normal120 4 6 65536 = cell130 := by
  calc
    rightChild 9 PR SL normal120 4 6 65536 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal120) 4 6 65536).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal120) 4 6 65536).symm
    _ = cell130 := by rfl
theorem normalized065 : AdaptiveCoverage.normalize SL cell130 = normal122 := by
  calc
    AdaptiveCoverage.normalize SL cell130 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell130)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell130)).symm
    _ = normal122 := by rfl
theorem left065 : leftChild 9 PR SL normal122 0 6 229376 = cell131 := by
  calc
    leftChild 9 PR SL normal122 0 6 229376 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal122) 0 6 229376).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal122) 0 6 229376).symm
    _ = cell131 := by rfl
theorem right065 : rightChild 9 PR SL normal122 0 6 229376 = cell132 := by
  calc
    rightChild 9 PR SL normal122 0 6 229376 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal122) 0 6 229376).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal122) 0 6 229376).symm
    _ = cell132 := by rfl
theorem normalized066 : AdaptiveCoverage.normalize SL cell131 = normal123 := by
  calc
    AdaptiveCoverage.normalize SL cell131 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell131)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell131)).symm
    _ = normal123 := by rfl
theorem left066 : leftChild 9 PR SL normal123 2 4 81920 = cell133 := by
  calc
    leftChild 9 PR SL normal123 2 4 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal123) 2 4 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal123) 2 4 81920).symm
    _ = cell133 := by rfl
theorem right066 : rightChild 9 PR SL normal123 2 4 81920 = cell134 := by
  calc
    rightChild 9 PR SL normal123 2 4 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal123) 2 4 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal123) 2 4 81920).symm
    _ = cell134 := by rfl
theorem normalized067 : AdaptiveCoverage.normalize SL cell106 = normal130 := by
  calc
    AdaptiveCoverage.normalize SL cell106 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell106)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell106)).symm
    _ = normal130 := by rfl
theorem left067 : leftChild 9 PR SL normal130 3 5 98304 = cell135 := by
  calc
    leftChild 9 PR SL normal130 3 5 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal130) 3 5 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal130) 3 5 98304).symm
    _ = cell135 := by rfl
theorem right067 : rightChild 9 PR SL normal130 3 5 98304 = cell136 := by
  calc
    rightChild 9 PR SL normal130 3 5 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal130) 3 5 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal130) 3 5 98304).symm
    _ = cell136 := by rfl
theorem normalized068 : AdaptiveCoverage.normalize SL cell135 = normal131 := by
  calc
    AdaptiveCoverage.normalize SL cell135 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell135)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell135)).symm
    _ = normal131 := by rfl
theorem left068 : leftChild 9 PR SL normal131 4 6 98304 = cell137 := by
  calc
    leftChild 9 PR SL normal131 4 6 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal131) 4 6 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal131) 4 6 98304).symm
    _ = cell137 := by rfl
theorem right068 : rightChild 9 PR SL normal131 4 6 98304 = cell138 := by
  calc
    rightChild 9 PR SL normal131 4 6 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal131) 4 6 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal131) 4 6 98304).symm
    _ = cell138 := by rfl
theorem normalized069 : AdaptiveCoverage.normalize SL cell137 = normal132 := by
  calc
    AdaptiveCoverage.normalize SL cell137 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell137)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell137)).symm
    _ = normal132 := by rfl
theorem left069 : leftChild 9 PR SL normal132 3 6 114688 = cell139 := by
  calc
    leftChild 9 PR SL normal132 3 6 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal132) 3 6 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal132) 3 6 114688).symm
    _ = cell139 := by rfl
theorem right069 : rightChild 9 PR SL normal132 3 6 114688 = cell140 := by
  calc
    rightChild 9 PR SL normal132 3 6 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal132) 3 6 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal132) 3 6 114688).symm
    _ = cell140 := by rfl
theorem normalized070 : AdaptiveCoverage.normalize SL cell140 = normal134 := by
  calc
    AdaptiveCoverage.normalize SL cell140 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell140)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell140)).symm
    _ = normal134 := by rfl
theorem left070 : leftChild 9 PR SL normal134 2 5 114688 = cell141 := by
  calc
    leftChild 9 PR SL normal134 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal134) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal134) 2 5 114688).symm
    _ = cell141 := by rfl
theorem right070 : rightChild 9 PR SL normal134 2 5 114688 = cell142 := by
  calc
    rightChild 9 PR SL normal134 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal134) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal134) 2 5 114688).symm
    _ = cell142 := by rfl
theorem normalized071 : AdaptiveCoverage.normalize SL cell141 = normal135 := by
  calc
    AdaptiveCoverage.normalize SL cell141 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell141)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell141)).symm
    _ = normal135 := by rfl
theorem left071 : leftChild 9 PR SL normal135 4 7 131072 = cell143 := by
  calc
    leftChild 9 PR SL normal135 4 7 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal135) 4 7 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal135) 4 7 131072).symm
    _ = cell143 := by rfl
theorem right071 : rightChild 9 PR SL normal135 4 7 131072 = cell144 := by
  calc
    rightChild 9 PR SL normal135 4 7 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal135) 4 7 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal135) 4 7 131072).symm
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
end StructuralGoal20261016.W10Aux127
end
