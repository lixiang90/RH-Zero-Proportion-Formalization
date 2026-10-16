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
theorem normalized192 : AdaptiveCoverage.normalize SL cell383 = normal368 := by
  calc
    AdaptiveCoverage.normalize SL cell383 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell383)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell383)).symm
    _ = normal368 := by rfl
theorem left192 : leftChild 9 PR SL normal368 3 6 98304 = cell385 := by
  calc
    leftChild 9 PR SL normal368 3 6 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal368) 3 6 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal368) 3 6 98304).symm
    _ = cell385 := by rfl
theorem right192 : rightChild 9 PR SL normal368 3 6 98304 = cell386 := by
  calc
    rightChild 9 PR SL normal368 3 6 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal368) 3 6 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal368) 3 6 98304).symm
    _ = cell386 := by rfl
theorem normalized193 : AdaptiveCoverage.normalize SL cell386 = normal370 := by
  calc
    AdaptiveCoverage.normalize SL cell386 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell386)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell386)).symm
    _ = normal370 := by rfl
theorem left193 : leftChild 9 PR SL normal370 4 7 98304 = cell387 := by
  calc
    leftChild 9 PR SL normal370 4 7 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal370) 4 7 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal370) 4 7 98304).symm
    _ = cell387 := by rfl
theorem right193 : rightChild 9 PR SL normal370 4 7 98304 = cell388 := by
  calc
    rightChild 9 PR SL normal370 4 7 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal370) 4 7 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal370) 4 7 98304).symm
    _ = cell388 := by rfl
theorem normalized194 : AdaptiveCoverage.normalize SL cell388 = normal372 := by
  calc
    AdaptiveCoverage.normalize SL cell388 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell388)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell388)).symm
    _ = normal372 := by rfl
theorem left194 : leftChild 9 PR SL normal372 2 6 147456 = cell389 := by
  calc
    leftChild 9 PR SL normal372 2 6 147456 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal372) 2 6 147456).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal372) 2 6 147456).symm
    _ = cell389 := by rfl
theorem right194 : rightChild 9 PR SL normal372 2 6 147456 = cell390 := by
  calc
    rightChild 9 PR SL normal372 2 6 147456 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal372) 2 6 147456).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal372) 2 6 147456).symm
    _ = cell390 := by rfl
theorem normalized195 : AdaptiveCoverage.normalize SL cell372 = normal380 := by
  calc
    AdaptiveCoverage.normalize SL cell372 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell372)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell372)).symm
    _ = normal380 := by rfl
theorem left195 : leftChild 9 PR SL normal380 3 5 81920 = cell391 := by
  calc
    leftChild 9 PR SL normal380 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal380) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal380) 3 5 81920).symm
    _ = cell391 := by rfl
theorem right195 : rightChild 9 PR SL normal380 3 5 81920 = cell392 := by
  calc
    rightChild 9 PR SL normal380 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal380) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal380) 3 5 81920).symm
    _ = cell392 := by rfl
theorem normalized196 : AdaptiveCoverage.normalize SL cell391 = normal381 := by
  calc
    AdaptiveCoverage.normalize SL cell391 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell391)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell391)).symm
    _ = normal381 := by rfl
theorem left196 : leftChild 9 PR SL normal381 4 6 81920 = cell393 := by
  calc
    leftChild 9 PR SL normal381 4 6 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal381) 4 6 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal381) 4 6 81920).symm
    _ = cell393 := by rfl
theorem right196 : rightChild 9 PR SL normal381 4 6 81920 = cell394 := by
  calc
    rightChild 9 PR SL normal381 4 6 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal381) 4 6 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal381) 4 6 81920).symm
    _ = cell394 := by rfl
theorem normalized197 : AdaptiveCoverage.normalize SL cell393 = normal382 := by
  calc
    AdaptiveCoverage.normalize SL cell393 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell393)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell393)).symm
    _ = normal382 := by rfl
theorem left197 : leftChild 9 PR SL normal382 1 9 294912 = cell395 := by
  calc
    leftChild 9 PR SL normal382 1 9 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal382) 1 9 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal382) 1 9 294912).symm
    _ = cell395 := by rfl
theorem right197 : rightChild 9 PR SL normal382 1 9 294912 = cell396 := by
  calc
    rightChild 9 PR SL normal382 1 9 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal382) 1 9 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal382) 1 9 294912).symm
    _ = cell396 := by rfl
theorem normalized198 : AdaptiveCoverage.normalize SL cell395 = normal383 := by
  calc
    AdaptiveCoverage.normalize SL cell395 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell395)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell395)).symm
    _ = normal383 := by rfl
theorem left198 : leftChild 9 PR SL normal383 0 6 229376 = cell397 := by
  calc
    leftChild 9 PR SL normal383 0 6 229376 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal383) 0 6 229376).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal383) 0 6 229376).symm
    _ = cell397 := by rfl
theorem right198 : rightChild 9 PR SL normal383 0 6 229376 = cell398 := by
  calc
    rightChild 9 PR SL normal383 0 6 229376 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal383) 0 6 229376).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal383) 0 6 229376).symm
    _ = cell398 := by rfl
theorem normalized199 : AdaptiveCoverage.normalize SL cell398 = normal385 := by
  calc
    AdaptiveCoverage.normalize SL cell398 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell398)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell398)).symm
    _ = normal385 := by rfl
theorem left199 : leftChild 9 PR SL normal385 2 5 114688 = cell399 := by
  calc
    leftChild 9 PR SL normal385 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal385) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal385) 2 5 114688).symm
    _ = cell399 := by rfl
theorem right199 : rightChild 9 PR SL normal385 2 5 114688 = cell400 := by
  calc
    rightChild 9 PR SL normal385 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal385) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal385) 2 5 114688).symm
    _ = cell400 := by rfl

set_option pp.fullNames true
#print axioms normalized192
#print axioms left192
#print axioms right192
#print axioms normalized193
#print axioms left193
#print axioms right193
#print axioms normalized194
#print axioms left194
#print axioms right194
#print axioms normalized195
#print axioms left195
#print axioms right195
#print axioms normalized196
#print axioms left196
#print axioms right196
#print axioms normalized197
#print axioms left197
#print axioms right197
#print axioms normalized198
#print axioms left198
#print axioms right198
#print axioms normalized199
#print axioms left199
#print axioms right199
end StructuralGoal20261016.W10Aux478
end
