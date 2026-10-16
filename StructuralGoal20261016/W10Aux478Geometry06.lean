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
theorem normalized048 : AdaptiveCoverage.normalize SL cell095 = normal086 := by
  calc
    AdaptiveCoverage.normalize SL cell095 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell095)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell095)).symm
    _ = normal086 := by rfl
theorem left048 : leftChild 9 PR SL normal086 2 6 131072 = cell097 := by
  calc
    leftChild 9 PR SL normal086 2 6 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal086) 2 6 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal086) 2 6 131072).symm
    _ = cell097 := by rfl
theorem right048 : rightChild 9 PR SL normal086 2 6 131072 = cell098 := by
  calc
    rightChild 9 PR SL normal086 2 6 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal086) 2 6 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal086) 2 6 131072).symm
    _ = cell098 := by rfl
theorem normalized049 : AdaptiveCoverage.normalize SL cell098 = normal088 := by
  calc
    AdaptiveCoverage.normalize SL cell098 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell098)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell098)).symm
    _ = normal088 := by rfl
theorem left049 : leftChild 9 PR SL normal088 1 9 294912 = cell099 := by
  calc
    leftChild 9 PR SL normal088 1 9 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal088) 1 9 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal088) 1 9 294912).symm
    _ = cell099 := by rfl
theorem right049 : rightChild 9 PR SL normal088 1 9 294912 = cell100 := by
  calc
    rightChild 9 PR SL normal088 1 9 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal088) 1 9 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal088) 1 9 294912).symm
    _ = cell100 := by rfl
theorem normalized050 : AdaptiveCoverage.normalize SL cell099 = normal089 := by
  calc
    AdaptiveCoverage.normalize SL cell099 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell099)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell099)).symm
    _ = normal089 := by rfl
theorem left050 : leftChild 9 PR SL normal089 0 8 294912 = cell101 := by
  calc
    leftChild 9 PR SL normal089 0 8 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal089) 0 8 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal089) 0 8 294912).symm
    _ = cell101 := by rfl
theorem right050 : rightChild 9 PR SL normal089 0 8 294912 = cell102 := by
  calc
    rightChild 9 PR SL normal089 0 8 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal089) 0 8 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal089) 0 8 294912).symm
    _ = cell102 := by rfl
theorem normalized051 : AdaptiveCoverage.normalize SL cell101 = normal090 := by
  calc
    AdaptiveCoverage.normalize SL cell101 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell101)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell101)).symm
    _ = normal090 := by rfl
theorem left051 : leftChild 9 PR SL normal090 3 5 81920 = cell103 := by
  calc
    leftChild 9 PR SL normal090 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal090) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal090) 3 5 81920).symm
    _ = cell103 := by rfl
theorem right051 : rightChild 9 PR SL normal090 3 5 81920 = cell104 := by
  calc
    rightChild 9 PR SL normal090 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal090) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal090) 3 5 81920).symm
    _ = cell104 := by rfl
theorem normalized052 : AdaptiveCoverage.normalize SL cell103 = normal091 := by
  calc
    AdaptiveCoverage.normalize SL cell103 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell103)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell103)).symm
    _ = normal091 := by rfl
theorem left052 : leftChild 9 PR SL normal091 4 6 81920 = cell105 := by
  calc
    leftChild 9 PR SL normal091 4 6 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal091) 4 6 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal091) 4 6 81920).symm
    _ = cell105 := by rfl
theorem right052 : rightChild 9 PR SL normal091 4 6 81920 = cell106 := by
  calc
    rightChild 9 PR SL normal091 4 6 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal091) 4 6 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal091) 4 6 81920).symm
    _ = cell106 := by rfl
theorem normalized053 : AdaptiveCoverage.normalize SL cell105 = normal092 := by
  calc
    AdaptiveCoverage.normalize SL cell105 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell105)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell105)).symm
    _ = normal092 := by rfl
theorem left053 : leftChild 9 PR SL normal092 0 9 335872 = cell107 := by
  calc
    leftChild 9 PR SL normal092 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal092) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal092) 0 9 335872).symm
    _ = cell107 := by rfl
theorem right053 : rightChild 9 PR SL normal092 0 9 335872 = cell108 := by
  calc
    rightChild 9 PR SL normal092 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal092) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal092) 0 9 335872).symm
    _ = cell108 := by rfl
theorem normalized054 : AdaptiveCoverage.normalize SL cell107 = normal093 := by
  calc
    AdaptiveCoverage.normalize SL cell107 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell107)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell107)).symm
    _ = normal093 := by rfl
theorem left054 : leftChild 9 PR SL normal093 4 7 98304 = cell109 := by
  calc
    leftChild 9 PR SL normal093 4 7 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal093) 4 7 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal093) 4 7 98304).symm
    _ = cell109 := by rfl
theorem right054 : rightChild 9 PR SL normal093 4 7 98304 = cell110 := by
  calc
    rightChild 9 PR SL normal093 4 7 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal093) 4 7 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal093) 4 7 98304).symm
    _ = cell110 := by rfl
theorem normalized055 : AdaptiveCoverage.normalize SL cell110 = normal095 := by
  calc
    AdaptiveCoverage.normalize SL cell110 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell110)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell110)).symm
    _ = normal095 := by rfl
theorem left055 : leftChild 9 PR SL normal095 5 7 81920 = cell111 := by
  calc
    leftChild 9 PR SL normal095 5 7 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal095) 5 7 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal095) 5 7 81920).symm
    _ = cell111 := by rfl
theorem right055 : rightChild 9 PR SL normal095 5 7 81920 = cell112 := by
  calc
    rightChild 9 PR SL normal095 5 7 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal095) 5 7 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal095) 5 7 81920).symm
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
end StructuralGoal20261016.W10Aux478
end
