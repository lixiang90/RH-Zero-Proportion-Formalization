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
theorem normalized280 : AdaptiveCoverage.normalize SL cell362 = normal553 := by
  calc
    AdaptiveCoverage.normalize SL cell362 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell362)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell362)).symm
    _ = normal553 := by rfl
theorem left280 : leftChild 9 PR SL normal553 2 6 131072 = cell561 := by
  calc
    leftChild 9 PR SL normal553 2 6 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal553) 2 6 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal553) 2 6 131072).symm
    _ = cell561 := by rfl
theorem right280 : rightChild 9 PR SL normal553 2 6 131072 = cell562 := by
  calc
    rightChild 9 PR SL normal553 2 6 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal553) 2 6 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal553) 2 6 131072).symm
    _ = cell562 := by rfl
theorem normalized281 : AdaptiveCoverage.normalize SL cell562 = normal555 := by
  calc
    AdaptiveCoverage.normalize SL cell562 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell562)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell562)).symm
    _ = normal555 := by rfl
theorem left281 : leftChild 9 PR SL normal555 3 7 131072 = cell563 := by
  calc
    leftChild 9 PR SL normal555 3 7 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal555) 3 7 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal555) 3 7 131072).symm
    _ = cell563 := by rfl
theorem right281 : rightChild 9 PR SL normal555 3 7 131072 = cell564 := by
  calc
    rightChild 9 PR SL normal555 3 7 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal555) 3 7 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal555) 3 7 131072).symm
    _ = cell564 := by rfl
theorem normalized282 : AdaptiveCoverage.normalize SL cell564 = normal557 := by
  calc
    AdaptiveCoverage.normalize SL cell564 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell564)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell564)).symm
    _ = normal557 := by rfl
theorem left282 : leftChild 9 PR SL normal557 1 6 196608 = cell565 := by
  calc
    leftChild 9 PR SL normal557 1 6 196608 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal557) 1 6 196608).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal557) 1 6 196608).symm
    _ = cell565 := by rfl
theorem right282 : rightChild 9 PR SL normal557 1 6 196608 = cell566 := by
  calc
    rightChild 9 PR SL normal557 1 6 196608 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal557) 1 6 196608).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal557) 1 6 196608).symm
    _ = cell566 := by rfl
theorem normalized283 : AdaptiveCoverage.normalize SL cell565 = normal558 := by
  calc
    AdaptiveCoverage.normalize SL cell565 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell565)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell565)).symm
    _ = normal558 := by rfl
theorem left283 : leftChild 9 PR SL normal558 3 8 196608 = cell567 := by
  calc
    leftChild 9 PR SL normal558 3 8 196608 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal558) 3 8 196608).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal558) 3 8 196608).symm
    _ = cell567 := by rfl
theorem right283 : rightChild 9 PR SL normal558 3 8 196608 = cell568 := by
  calc
    rightChild 9 PR SL normal558 3 8 196608 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal558) 3 8 196608).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal558) 3 8 196608).symm
    _ = cell568 := by rfl
theorem normalized284 : AdaptiveCoverage.normalize SL cell567 = normal559 := by
  calc
    AdaptiveCoverage.normalize SL cell567 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell567)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell567)).symm
    _ = normal559 := by rfl
theorem left284 : leftChild 9 PR SL normal559 3 5 81920 = cell569 := by
  calc
    leftChild 9 PR SL normal559 3 5 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal559) 3 5 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal559) 3 5 81920).symm
    _ = cell569 := by rfl
theorem right284 : rightChild 9 PR SL normal559 3 5 81920 = cell570 := by
  calc
    rightChild 9 PR SL normal559 3 5 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal559) 3 5 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal559) 3 5 81920).symm
    _ = cell570 := by rfl
theorem normalized285 : AdaptiveCoverage.normalize SL cell569 = normal560 := by
  calc
    AdaptiveCoverage.normalize SL cell569 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell569)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell569)).symm
    _ = normal560 := by rfl
theorem left285 : leftChild 9 PR SL normal560 4 6 81920 = cell571 := by
  calc
    leftChild 9 PR SL normal560 4 6 81920 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal560) 4 6 81920).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal560) 4 6 81920).symm
    _ = cell571 := by rfl
theorem right285 : rightChild 9 PR SL normal560 4 6 81920 = cell572 := by
  calc
    rightChild 9 PR SL normal560 4 6 81920 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal560) 4 6 81920).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal560) 4 6 81920).symm
    _ = cell572 := by rfl
theorem normalized286 : AdaptiveCoverage.normalize SL cell571 = normal561 := by
  calc
    AdaptiveCoverage.normalize SL cell571 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell571)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell571)).symm
    _ = normal561 := by rfl
theorem left286 : leftChild 9 PR SL normal561 0 8 294912 = cell573 := by
  calc
    leftChild 9 PR SL normal561 0 8 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal561) 0 8 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal561) 0 8 294912).symm
    _ = cell573 := by rfl
theorem right286 : rightChild 9 PR SL normal561 0 8 294912 = cell574 := by
  calc
    rightChild 9 PR SL normal561 0 8 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal561) 0 8 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal561) 0 8 294912).symm
    _ = cell574 := by rfl
theorem normalized287 : AdaptiveCoverage.normalize SL cell573 = normal562 := by
  calc
    AdaptiveCoverage.normalize SL cell573 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell573)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell573)).symm
    _ = normal562 := by rfl
theorem left287 : leftChild 9 PR SL normal562 1 9 294912 = cell575 := by
  calc
    leftChild 9 PR SL normal562 1 9 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal562) 1 9 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal562) 1 9 294912).symm
    _ = cell575 := by rfl
theorem right287 : rightChild 9 PR SL normal562 1 9 294912 = cell576 := by
  calc
    rightChild 9 PR SL normal562 1 9 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal562) 1 9 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal562) 1 9 294912).symm
    _ = cell576 := by rfl

set_option pp.fullNames true
#print axioms normalized280
#print axioms left280
#print axioms right280
#print axioms normalized281
#print axioms left281
#print axioms right281
#print axioms normalized282
#print axioms left282
#print axioms right282
#print axioms normalized283
#print axioms left283
#print axioms right283
#print axioms normalized284
#print axioms left284
#print axioms right284
#print axioms normalized285
#print axioms left285
#print axioms right285
#print axioms normalized286
#print axioms left286
#print axioms right286
#print axioms normalized287
#print axioms left287
#print axioms right287
end StructuralGoal20261016.W10Aux478
end
