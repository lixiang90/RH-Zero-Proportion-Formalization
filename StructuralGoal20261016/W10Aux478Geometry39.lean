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
theorem normalized312 : AdaptiveCoverage.normalize SL cell620 = normal612 := by
  calc
    AdaptiveCoverage.normalize SL cell620 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell620)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell620)).symm
    _ = normal612 := by rfl
theorem left312 : leftChild 9 PR SL normal612 5 6 49152 = cell625 := by
  calc
    leftChild 9 PR SL normal612 5 6 49152 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal612) 5 6 49152).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal612) 5 6 49152).symm
    _ = cell625 := by rfl
theorem right312 : rightChild 9 PR SL normal612 5 6 49152 = cell626 := by
  calc
    rightChild 9 PR SL normal612 5 6 49152 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal612) 5 6 49152).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal612) 5 6 49152).symm
    _ = cell626 := by rfl
theorem normalized313 : AdaptiveCoverage.normalize SL cell616 = normal616 := by
  calc
    AdaptiveCoverage.normalize SL cell616 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell616)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell616)).symm
    _ = normal616 := by rfl
theorem left313 : leftChild 9 PR SL normal616 2 5 114688 = cell627 := by
  calc
    leftChild 9 PR SL normal616 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal616) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal616) 2 5 114688).symm
    _ = cell627 := by rfl
theorem right313 : rightChild 9 PR SL normal616 2 5 114688 = cell628 := by
  calc
    rightChild 9 PR SL normal616 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal616) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal616) 2 5 114688).symm
    _ = cell628 := by rfl
theorem normalized314 : AdaptiveCoverage.normalize SL cell627 = normal617 := by
  calc
    AdaptiveCoverage.normalize SL cell627 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell627)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell627)).symm
    _ = normal617 := by rfl
theorem left314 : leftChild 9 PR SL normal617 0 7 262144 = cell629 := by
  calc
    leftChild 9 PR SL normal617 0 7 262144 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal617) 0 7 262144).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal617) 0 7 262144).symm
    _ = cell629 := by rfl
theorem right314 : rightChild 9 PR SL normal617 0 7 262144 = cell630 := by
  calc
    rightChild 9 PR SL normal617 0 7 262144 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal617) 0 7 262144).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal617) 0 7 262144).symm
    _ = cell630 := by rfl
theorem normalized315 : AdaptiveCoverage.normalize SL cell629 = normal618 := by
  calc
    AdaptiveCoverage.normalize SL cell629 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell629)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell629)).symm
    _ = normal618 := by rfl
theorem left315 : leftChild 9 PR SL normal618 2 9 262144 = cell631 := by
  calc
    leftChild 9 PR SL normal618 2 9 262144 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal618) 2 9 262144).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal618) 2 9 262144).symm
    _ = cell631 := by rfl
theorem right315 : rightChild 9 PR SL normal618 2 9 262144 = cell632 := by
  calc
    rightChild 9 PR SL normal618 2 9 262144 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal618) 2 9 262144).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal618) 2 9 262144).symm
    _ = cell632 := by rfl
theorem normalized316 : AdaptiveCoverage.normalize SL cell631 = normal619 := by
  calc
    AdaptiveCoverage.normalize SL cell631 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell631)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell631)).symm
    _ = normal619 := by rfl
theorem left316 : leftChild 9 PR SL normal619 5 6 49152 = cell633 := by
  calc
    leftChild 9 PR SL normal619 5 6 49152 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal619) 5 6 49152).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal619) 5 6 49152).symm
    _ = cell633 := by rfl
theorem right316 : rightChild 9 PR SL normal619 5 6 49152 = cell634 := by
  calc
    rightChild 9 PR SL normal619 5 6 49152 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal619) 5 6 49152).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal619) 5 6 49152).symm
    _ = cell634 := by rfl
theorem normalized317 : AdaptiveCoverage.normalize SL cell632 = normal622 := by
  calc
    AdaptiveCoverage.normalize SL cell632 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell632)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell632)).symm
    _ = normal622 := by rfl
theorem left317 : leftChild 9 PR SL normal622 5 6 49152 = cell635 := by
  calc
    leftChild 9 PR SL normal622 5 6 49152 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal622) 5 6 49152).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal622) 5 6 49152).symm
    _ = cell635 := by rfl
theorem right317 : rightChild 9 PR SL normal622 5 6 49152 = cell636 := by
  calc
    rightChild 9 PR SL normal622 5 6 49152 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal622) 5 6 49152).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal622) 5 6 49152).symm
    _ = cell636 := by rfl
theorem normalized318 : AdaptiveCoverage.normalize SL cell630 = normal625 := by
  calc
    AdaptiveCoverage.normalize SL cell630 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell630)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell630)).symm
    _ = normal625 := by rfl
theorem left318 : leftChild 9 PR SL normal625 5 6 61008 = cell637 := by
  calc
    leftChild 9 PR SL normal625 5 6 61008 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal625) 5 6 61008).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal625) 5 6 61008).symm
    _ = cell637 := by rfl
theorem right318 : rightChild 9 PR SL normal625 5 6 61008 = cell638 := by
  calc
    rightChild 9 PR SL normal625 5 6 61008 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal625) 5 6 61008).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal625) 5 6 61008).symm
    _ = cell638 := by rfl
theorem normalized319 : AdaptiveCoverage.normalize SL cell570 = normal629 := by
  calc
    AdaptiveCoverage.normalize SL cell570 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell570)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell570)).symm
    _ = normal629 := by rfl
theorem left319 : leftChild 9 PR SL normal629 3 4 60267 = cell639 := by
  calc
    leftChild 9 PR SL normal629 3 4 60267 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal629) 3 4 60267).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal629) 3 4 60267).symm
    _ = cell639 := by rfl
theorem right319 : rightChild 9 PR SL normal629 3 4 60267 = cell640 := by
  calc
    rightChild 9 PR SL normal629 3 4 60267 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal629) 3 4 60267).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal629) 3 4 60267).symm
    _ = cell640 := by rfl

set_option pp.fullNames true
#print axioms normalized312
#print axioms left312
#print axioms right312
#print axioms normalized313
#print axioms left313
#print axioms right313
#print axioms normalized314
#print axioms left314
#print axioms right314
#print axioms normalized315
#print axioms left315
#print axioms right315
#print axioms normalized316
#print axioms left316
#print axioms right316
#print axioms normalized317
#print axioms left317
#print axioms right317
#print axioms normalized318
#print axioms left318
#print axioms right318
#print axioms normalized319
#print axioms left319
#print axioms right319
end StructuralGoal20261016.W10Aux478
end
