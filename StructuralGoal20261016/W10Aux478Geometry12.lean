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
theorem normalized096 : AdaptiveCoverage.normalize SL cell192 = normal179 := by
  calc
    AdaptiveCoverage.normalize SL cell192 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell192)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell192)).symm
    _ = normal179 := by rfl
theorem left096 : leftChild 9 PR SL normal179 5 7 81920 = cell193 := by
  calc
    leftChild 9 PR SL normal179 5 7 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal179) 5 7 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal179) 5 7 81920).symm
    _ = cell193 := by rfl
theorem right096 : rightChild 9 PR SL normal179 5 7 81920 = cell194 := by
  calc
    rightChild 9 PR SL normal179 5 7 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal179) 5 7 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal179) 5 7 81920).symm
    _ = cell194 := by rfl
theorem normalized097 : AdaptiveCoverage.normalize SL cell186 = normal183 := by
  calc
    AdaptiveCoverage.normalize SL cell186 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell186)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell186)).symm
    _ = normal183 := by rfl
theorem left097 : leftChild 9 PR SL normal183 0 9 335872 = cell195 := by
  calc
    leftChild 9 PR SL normal183 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal183) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal183) 0 9 335872).symm
    _ = cell195 := by rfl
theorem right097 : rightChild 9 PR SL normal183 0 9 335872 = cell196 := by
  calc
    rightChild 9 PR SL normal183 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal183) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal183) 0 9 335872).symm
    _ = cell196 := by rfl
theorem normalized098 : AdaptiveCoverage.normalize SL cell195 = normal184 := by
  calc
    AdaptiveCoverage.normalize SL cell195 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell195)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell195)).symm
    _ = normal184 := by rfl
theorem left098 : leftChild 9 PR SL normal184 2 6 131072 = cell197 := by
  calc
    leftChild 9 PR SL normal184 2 6 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal184) 2 6 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal184) 2 6 131072).symm
    _ = cell197 := by rfl
theorem right098 : rightChild 9 PR SL normal184 2 6 131072 = cell198 := by
  calc
    rightChild 9 PR SL normal184 2 6 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal184) 2 6 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal184) 2 6 131072).symm
    _ = cell198 := by rfl
theorem normalized099 : AdaptiveCoverage.normalize SL cell198 = normal186 := by
  calc
    AdaptiveCoverage.normalize SL cell198 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell198)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell198)).symm
    _ = normal186 := by rfl
theorem left099 : leftChild 9 PR SL normal186 4 7 114688 = cell199 := by
  calc
    leftChild 9 PR SL normal186 4 7 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal186) 4 7 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal186) 4 7 114688).symm
    _ = cell199 := by rfl
theorem right099 : rightChild 9 PR SL normal186 4 7 114688 = cell200 := by
  calc
    rightChild 9 PR SL normal186 4 7 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal186) 4 7 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal186) 4 7 114688).symm
    _ = cell200 := by rfl
theorem normalized100 : AdaptiveCoverage.normalize SL cell200 = normal188 := by
  calc
    AdaptiveCoverage.normalize SL cell200 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell200)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell200)).symm
    _ = normal188 := by rfl
theorem left100 : leftChild 9 PR SL normal188 5 7 81920 = cell201 := by
  calc
    leftChild 9 PR SL normal188 5 7 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal188) 5 7 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal188) 5 7 81920).symm
    _ = cell201 := by rfl
theorem right100 : rightChild 9 PR SL normal188 5 7 81920 = cell202 := by
  calc
    rightChild 9 PR SL normal188 5 7 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal188) 5 7 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal188) 5 7 81920).symm
    _ = cell202 := by rfl
theorem normalized101 : AdaptiveCoverage.normalize SL cell184 = normal192 := by
  calc
    AdaptiveCoverage.normalize SL cell184 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell184)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell184)).symm
    _ = normal192 := by rfl
theorem left101 : leftChild 9 PR SL normal192 1 9 294912 = cell203 := by
  calc
    leftChild 9 PR SL normal192 1 9 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal192) 1 9 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal192) 1 9 294912).symm
    _ = cell203 := by rfl
theorem right101 : rightChild 9 PR SL normal192 1 9 294912 = cell204 := by
  calc
    rightChild 9 PR SL normal192 1 9 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal192) 1 9 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal192) 1 9 294912).symm
    _ = cell204 := by rfl
theorem normalized102 : AdaptiveCoverage.normalize SL cell203 = normal193 := by
  calc
    AdaptiveCoverage.normalize SL cell203 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell203)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell203)).symm
    _ = normal193 := by rfl
theorem left102 : leftChild 9 PR SL normal193 0 9 335872 = cell205 := by
  calc
    leftChild 9 PR SL normal193 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal193) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal193) 0 9 335872).symm
    _ = cell205 := by rfl
theorem right102 : rightChild 9 PR SL normal193 0 9 335872 = cell206 := by
  calc
    rightChild 9 PR SL normal193 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal193) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal193) 0 9 335872).symm
    _ = cell206 := by rfl
theorem normalized103 : AdaptiveCoverage.normalize SL cell205 = normal194 := by
  calc
    AdaptiveCoverage.normalize SL cell205 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell205)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell205)).symm
    _ = normal194 := by rfl
theorem left103 : leftChild 9 PR SL normal194 2 6 131072 = cell207 := by
  calc
    leftChild 9 PR SL normal194 2 6 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal194) 2 6 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal194) 2 6 131072).symm
    _ = cell207 := by rfl
theorem right103 : rightChild 9 PR SL normal194 2 6 131072 = cell208 := by
  calc
    rightChild 9 PR SL normal194 2 6 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal194) 2 6 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal194) 2 6 131072).symm
    _ = cell208 := by rfl

set_option pp.fullNames true
#print axioms normalized096
#print axioms left096
#print axioms right096
#print axioms normalized097
#print axioms left097
#print axioms right097
#print axioms normalized098
#print axioms left098
#print axioms right098
#print axioms normalized099
#print axioms left099
#print axioms right099
#print axioms normalized100
#print axioms left100
#print axioms right100
#print axioms normalized101
#print axioms left101
#print axioms right101
#print axioms normalized102
#print axioms left102
#print axioms right102
#print axioms normalized103
#print axioms left103
#print axioms right103
end StructuralGoal20261016.W10Aux478
end
