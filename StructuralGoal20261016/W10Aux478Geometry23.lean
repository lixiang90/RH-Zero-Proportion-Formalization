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
theorem normalized184 : AdaptiveCoverage.normalize SL cell367 = normal358 := by
  calc
    AdaptiveCoverage.normalize SL cell367 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell367)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell367)).symm
    _ = normal358 := by rfl
theorem left184 : leftChild 9 PR SL normal358 3 7 131072 = cell369 := by
  calc
    leftChild 9 PR SL normal358 3 7 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal358) 3 7 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal358) 3 7 131072).symm
    _ = cell369 := by rfl
theorem right184 : rightChild 9 PR SL normal358 3 7 131072 = cell370 := by
  calc
    rightChild 9 PR SL normal358 3 7 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal358) 3 7 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal358) 3 7 131072).symm
    _ = cell370 := by rfl
theorem normalized185 : AdaptiveCoverage.normalize SL cell370 = normal360 := by
  calc
    AdaptiveCoverage.normalize SL cell370 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell370)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell370)).symm
    _ = normal360 := by rfl
theorem left185 : leftChild 9 PR SL normal360 0 8 294912 = cell371 := by
  calc
    leftChild 9 PR SL normal360 0 8 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal360) 0 8 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal360) 0 8 294912).symm
    _ = cell371 := by rfl
theorem right185 : rightChild 9 PR SL normal360 0 8 294912 = cell372 := by
  calc
    rightChild 9 PR SL normal360 0 8 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal360) 0 8 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal360) 0 8 294912).symm
    _ = cell372 := by rfl
theorem normalized186 : AdaptiveCoverage.normalize SL cell371 = normal361 := by
  calc
    AdaptiveCoverage.normalize SL cell371 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell371)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell371)).symm
    _ = normal361 := by rfl
theorem left186 : leftChild 9 PR SL normal361 1 9 294912 = cell373 := by
  calc
    leftChild 9 PR SL normal361 1 9 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal361) 1 9 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal361) 1 9 294912).symm
    _ = cell373 := by rfl
theorem right186 : rightChild 9 PR SL normal361 1 9 294912 = cell374 := by
  calc
    rightChild 9 PR SL normal361 1 9 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal361) 1 9 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal361) 1 9 294912).symm
    _ = cell374 := by rfl
theorem normalized187 : AdaptiveCoverage.normalize SL cell373 = normal362 := by
  calc
    AdaptiveCoverage.normalize SL cell373 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell373)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell373)).symm
    _ = normal362 := by rfl
theorem left187 : leftChild 9 PR SL normal362 3 5 81920 = cell375 := by
  calc
    leftChild 9 PR SL normal362 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal362) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal362) 3 5 81920).symm
    _ = cell375 := by rfl
theorem right187 : rightChild 9 PR SL normal362 3 5 81920 = cell376 := by
  calc
    rightChild 9 PR SL normal362 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal362) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal362) 3 5 81920).symm
    _ = cell376 := by rfl
theorem normalized188 : AdaptiveCoverage.normalize SL cell375 = normal363 := by
  calc
    AdaptiveCoverage.normalize SL cell375 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell375)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell375)).symm
    _ = normal363 := by rfl
theorem left188 : leftChild 9 PR SL normal363 4 6 81920 = cell377 := by
  calc
    leftChild 9 PR SL normal363 4 6 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal363) 4 6 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal363) 4 6 81920).symm
    _ = cell377 := by rfl
theorem right188 : rightChild 9 PR SL normal363 4 6 81920 = cell378 := by
  calc
    rightChild 9 PR SL normal363 4 6 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal363) 4 6 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal363) 4 6 81920).symm
    _ = cell378 := by rfl
theorem normalized189 : AdaptiveCoverage.normalize SL cell377 = normal364 := by
  calc
    AdaptiveCoverage.normalize SL cell377 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell377)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell377)).symm
    _ = normal364 := by rfl
theorem left189 : leftChild 9 PR SL normal364 0 9 335872 = cell379 := by
  calc
    leftChild 9 PR SL normal364 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal364) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal364) 0 9 335872).symm
    _ = cell379 := by rfl
theorem right189 : rightChild 9 PR SL normal364 0 9 335872 = cell380 := by
  calc
    rightChild 9 PR SL normal364 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal364) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal364) 0 9 335872).symm
    _ = cell380 := by rfl
theorem normalized190 : AdaptiveCoverage.normalize SL cell379 = normal365 := by
  calc
    AdaptiveCoverage.normalize SL cell379 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell379)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell379)).symm
    _ = normal365 := by rfl
theorem left190 : leftChild 9 PR SL normal365 2 5 98304 = cell381 := by
  calc
    leftChild 9 PR SL normal365 2 5 98304 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal365) 2 5 98304).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal365) 2 5 98304).symm
    _ = cell381 := by rfl
theorem right190 : rightChild 9 PR SL normal365 2 5 98304 = cell382 := by
  calc
    rightChild 9 PR SL normal365 2 5 98304 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal365) 2 5 98304).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal365) 2 5 98304).symm
    _ = cell382 := by rfl
theorem normalized191 : AdaptiveCoverage.normalize SL cell382 = normal367 := by
  calc
    AdaptiveCoverage.normalize SL cell382 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell382)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell382)).symm
    _ = normal367 := by rfl
theorem left191 : leftChild 9 PR SL normal367 2 4 81920 = cell383 := by
  calc
    leftChild 9 PR SL normal367 2 4 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal367) 2 4 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal367) 2 4 81920).symm
    _ = cell383 := by rfl
theorem right191 : rightChild 9 PR SL normal367 2 4 81920 = cell384 := by
  calc
    rightChild 9 PR SL normal367 2 4 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal367) 2 4 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal367) 2 4 81920).symm
    _ = cell384 := by rfl

set_option pp.fullNames true
#print axioms normalized184
#print axioms left184
#print axioms right184
#print axioms normalized185
#print axioms left185
#print axioms right185
#print axioms normalized186
#print axioms left186
#print axioms right186
#print axioms normalized187
#print axioms left187
#print axioms right187
#print axioms normalized188
#print axioms left188
#print axioms right188
#print axioms normalized189
#print axioms left189
#print axioms right189
#print axioms normalized190
#print axioms left190
#print axioms right190
#print axioms normalized191
#print axioms left191
#print axioms right191
end StructuralGoal20261016.W10Aux478
end
