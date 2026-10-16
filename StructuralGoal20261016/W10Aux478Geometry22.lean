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
theorem normalized176 : AdaptiveCoverage.normalize SL cell352 = normal342 := by
  calc
    AdaptiveCoverage.normalize SL cell352 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell352)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell352)).symm
    _ = normal342 := by rfl
theorem left176 : leftChild 9 PR SL normal342 1 8 262144 = cell353 := by
  calc
    leftChild 9 PR SL normal342 1 8 262144 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal342) 1 8 262144).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal342) 1 8 262144).symm
    _ = cell353 := by rfl
theorem right176 : rightChild 9 PR SL normal342 1 8 262144 = cell354 := by
  calc
    rightChild 9 PR SL normal342 1 8 262144 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal342) 1 8 262144).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal342) 1 8 262144).symm
    _ = cell354 := by rfl
theorem normalized177 : AdaptiveCoverage.normalize SL cell354 = normal344 := by
  calc
    AdaptiveCoverage.normalize SL cell354 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell354)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell354)).symm
    _ = normal344 := by rfl
theorem left177 : leftChild 9 PR SL normal344 2 4 81920 = cell355 := by
  calc
    leftChild 9 PR SL normal344 2 4 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal344) 2 4 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal344) 2 4 81920).symm
    _ = cell355 := by rfl
theorem right177 : rightChild 9 PR SL normal344 2 4 81920 = cell356 := by
  calc
    rightChild 9 PR SL normal344 2 4 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal344) 2 4 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal344) 2 4 81920).symm
    _ = cell356 := by rfl
theorem normalized178 : AdaptiveCoverage.normalize SL cell355 = normal345 := by
  calc
    AdaptiveCoverage.normalize SL cell355 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell355)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell355)).symm
    _ = normal345 := by rfl
theorem left178 : leftChild 9 PR SL normal345 4 8 180224 = cell357 := by
  calc
    leftChild 9 PR SL normal345 4 8 180224 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal345) 4 8 180224).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal345) 4 8 180224).symm
    _ = cell357 := by rfl
theorem right178 : rightChild 9 PR SL normal345 4 8 180224 = cell358 := by
  calc
    rightChild 9 PR SL normal345 4 8 180224 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal345) 4 8 180224).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal345) 4 8 180224).symm
    _ = cell358 := by rfl
theorem normalized179 : AdaptiveCoverage.normalize SL cell357 = normal346 := by
  calc
    AdaptiveCoverage.normalize SL cell357 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell357)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell357)).symm
    _ = normal346 := by rfl
theorem left179 : leftChild 9 PR SL normal346 2 6 147456 = cell359 := by
  calc
    leftChild 9 PR SL normal346 2 6 147456 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal346) 2 6 147456).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal346) 2 6 147456).symm
    _ = cell359 := by rfl
theorem right179 : rightChild 9 PR SL normal346 2 6 147456 = cell360 := by
  calc
    rightChild 9 PR SL normal346 2 6 147456 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal346) 2 6 147456).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal346) 2 6 147456).symm
    _ = cell360 := by rfl
theorem normalized180 : AdaptiveCoverage.normalize SL cell090 = normal353 := by
  calc
    AdaptiveCoverage.normalize SL cell090 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell090)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell090)).symm
    _ = normal353 := by rfl
theorem left180 : leftChild 9 PR SL normal353 3 9 212992 = cell361 := by
  calc
    leftChild 9 PR SL normal353 3 9 212992 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal353) 3 9 212992).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal353) 3 9 212992).symm
    _ = cell361 := by rfl
theorem right180 : rightChild 9 PR SL normal353 3 9 212992 = cell362 := by
  calc
    rightChild 9 PR SL normal353 3 9 212992 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal353) 3 9 212992).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal353) 3 9 212992).symm
    _ = cell362 := by rfl
theorem normalized181 : AdaptiveCoverage.normalize SL cell361 = normal354 := by
  calc
    AdaptiveCoverage.normalize SL cell361 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell361)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell361)).symm
    _ = normal354 := by rfl
theorem left181 : leftChild 9 PR SL normal354 2 6 131072 = cell363 := by
  calc
    leftChild 9 PR SL normal354 2 6 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal354) 2 6 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal354) 2 6 131072).symm
    _ = cell363 := by rfl
theorem right181 : rightChild 9 PR SL normal354 2 6 131072 = cell364 := by
  calc
    rightChild 9 PR SL normal354 2 6 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal354) 2 6 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal354) 2 6 131072).symm
    _ = cell364 := by rfl
theorem normalized182 : AdaptiveCoverage.normalize SL cell364 = normal356 := by
  calc
    AdaptiveCoverage.normalize SL cell364 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell364)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell364)).symm
    _ = normal356 := by rfl
theorem left182 : leftChild 9 PR SL normal356 2 9 245760 = cell365 := by
  calc
    leftChild 9 PR SL normal356 2 9 245760 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal356) 2 9 245760).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal356) 2 9 245760).symm
    _ = cell365 := by rfl
theorem right182 : rightChild 9 PR SL normal356 2 9 245760 = cell366 := by
  calc
    rightChild 9 PR SL normal356 2 9 245760 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal356) 2 9 245760).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal356) 2 9 245760).symm
    _ = cell366 := by rfl
theorem normalized183 : AdaptiveCoverage.normalize SL cell365 = normal357 := by
  calc
    AdaptiveCoverage.normalize SL cell365 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell365)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell365)).symm
    _ = normal357 := by rfl
theorem left183 : leftChild 9 PR SL normal357 1 6 196608 = cell367 := by
  calc
    leftChild 9 PR SL normal357 1 6 196608 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal357) 1 6 196608).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal357) 1 6 196608).symm
    _ = cell367 := by rfl
theorem right183 : rightChild 9 PR SL normal357 1 6 196608 = cell368 := by
  calc
    rightChild 9 PR SL normal357 1 6 196608 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal357) 1 6 196608).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal357) 1 6 196608).symm
    _ = cell368 := by rfl

set_option pp.fullNames true
#print axioms normalized176
#print axioms left176
#print axioms right176
#print axioms normalized177
#print axioms left177
#print axioms right177
#print axioms normalized178
#print axioms left178
#print axioms right178
#print axioms normalized179
#print axioms left179
#print axioms right179
#print axioms normalized180
#print axioms left180
#print axioms right180
#print axioms normalized181
#print axioms left181
#print axioms right181
#print axioms normalized182
#print axioms left182
#print axioms right182
#print axioms normalized183
#print axioms left183
#print axioms right183
end StructuralGoal20261016.W10Aux478
end
