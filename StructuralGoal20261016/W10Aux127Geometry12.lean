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
theorem normalized096 : AdaptiveCoverage.normalize SL cell192 = normal181 := by
  calc
    AdaptiveCoverage.normalize SL cell192 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell192)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell192)).symm
    _ = normal181 := by rfl
theorem left096 : leftChild 9 PR SL normal181 3 8 196608 = cell193 := by
  calc
    leftChild 9 PR SL normal181 3 8 196608 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal181) 3 8 196608).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal181) 3 8 196608).symm
    _ = cell193 := by rfl
theorem right096 : rightChild 9 PR SL normal181 3 8 196608 = cell194 := by
  calc
    rightChild 9 PR SL normal181 3 8 196608 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal181) 3 8 196608).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal181) 3 8 196608).symm
    _ = cell194 := by rfl
theorem normalized097 : AdaptiveCoverage.normalize SL cell193 = normal182 := by
  calc
    AdaptiveCoverage.normalize SL cell193 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell193)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell193)).symm
    _ = normal182 := by rfl
theorem left097 : leftChild 9 PR SL normal182 3 4 49152 = cell195 := by
  calc
    leftChild 9 PR SL normal182 3 4 49152 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal182) 3 4 49152).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal182) 3 4 49152).symm
    _ = cell195 := by rfl
theorem right097 : rightChild 9 PR SL normal182 3 4 49152 = cell196 := by
  calc
    rightChild 9 PR SL normal182 3 4 49152 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal182) 3 4 49152).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal182) 3 4 49152).symm
    _ = cell196 := by rfl
theorem normalized098 : AdaptiveCoverage.normalize SL cell194 = normal185 := by
  calc
    AdaptiveCoverage.normalize SL cell194 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell194)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell194)).symm
    _ = normal185 := by rfl
theorem left098 : leftChild 9 PR SL normal185 3 4 49152 = cell197 := by
  calc
    leftChild 9 PR SL normal185 3 4 49152 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal185) 3 4 49152).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal185) 3 4 49152).symm
    _ = cell197 := by rfl
theorem right098 : rightChild 9 PR SL normal185 3 4 49152 = cell198 := by
  calc
    rightChild 9 PR SL normal185 3 4 49152 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal185) 3 4 49152).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal185) 3 4 49152).symm
    _ = cell198 := by rfl
theorem normalized099 : AdaptiveCoverage.normalize SL cell184 = normal188 := by
  calc
    AdaptiveCoverage.normalize SL cell184 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell184)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell184)).symm
    _ = normal188 := by rfl
theorem left099 : leftChild 9 PR SL normal188 1 4 131072 = cell199 := by
  calc
    leftChild 9 PR SL normal188 1 4 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal188) 1 4 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal188) 1 4 131072).symm
    _ = cell199 := by rfl
theorem right099 : rightChild 9 PR SL normal188 1 4 131072 = cell200 := by
  calc
    rightChild 9 PR SL normal188 1 4 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal188) 1 4 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal188) 1 4 131072).symm
    _ = cell200 := by rfl
theorem normalized100 : AdaptiveCoverage.normalize SL cell199 = normal189 := by
  calc
    AdaptiveCoverage.normalize SL cell199 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell199)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell199)).symm
    _ = normal189 := by rfl
theorem left100 : leftChild 9 PR SL normal189 3 5 81920 = cell201 := by
  calc
    leftChild 9 PR SL normal189 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal189) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal189) 3 5 81920).symm
    _ = cell201 := by rfl
theorem right100 : rightChild 9 PR SL normal189 3 5 81920 = cell202 := by
  calc
    rightChild 9 PR SL normal189 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal189) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal189) 3 5 81920).symm
    _ = cell202 := by rfl
theorem normalized101 : AdaptiveCoverage.normalize SL cell176 = normal194 := by
  calc
    AdaptiveCoverage.normalize SL cell176 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell176)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell176)).symm
    _ = normal194 := by rfl
theorem left101 : leftChild 9 PR SL normal194 3 7 163840 = cell203 := by
  calc
    leftChild 9 PR SL normal194 3 7 163840 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal194) 3 7 163840).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal194) 3 7 163840).symm
    _ = cell203 := by rfl
theorem right101 : rightChild 9 PR SL normal194 3 7 163840 = cell204 := by
  calc
    rightChild 9 PR SL normal194 3 7 163840 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal194) 3 7 163840).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal194) 3 7 163840).symm
    _ = cell204 := by rfl
theorem normalized102 : AdaptiveCoverage.normalize SL cell203 = normal195 := by
  calc
    AdaptiveCoverage.normalize SL cell203 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell203)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell203)).symm
    _ = normal195 := by rfl
theorem left102 : leftChild 9 PR SL normal195 0 9 319488 = cell205 := by
  calc
    leftChild 9 PR SL normal195 0 9 319488 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal195) 0 9 319488).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal195) 0 9 319488).symm
    _ = cell205 := by rfl
theorem right102 : rightChild 9 PR SL normal195 0 9 319488 = cell206 := by
  calc
    rightChild 9 PR SL normal195 0 9 319488 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal195) 0 9 319488).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal195) 0 9 319488).symm
    _ = cell206 := by rfl
theorem normalized103 : AdaptiveCoverage.normalize SL cell206 = normal197 := by
  calc
    AdaptiveCoverage.normalize SL cell206 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell206)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell206)).symm
    _ = normal197 := by rfl
theorem left103 : leftChild 9 PR SL normal197 3 5 81920 = cell207 := by
  calc
    leftChild 9 PR SL normal197 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal197) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal197) 3 5 81920).symm
    _ = cell207 := by rfl
theorem right103 : rightChild 9 PR SL normal197 3 5 81920 = cell208 := by
  calc
    rightChild 9 PR SL normal197 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal197) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal197) 3 5 81920).symm
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
end StructuralGoal20261016.W10Aux127
end
