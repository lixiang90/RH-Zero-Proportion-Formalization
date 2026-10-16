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
theorem normalized296 : AdaptiveCoverage.normalize SL cell591 = normal579 := by
  calc
    AdaptiveCoverage.normalize SL cell591 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell591)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell591)).symm
    _ = normal579 := by rfl
theorem left296 : leftChild 9 PR SL normal579 4 7 114688 = cell593 := by
  calc
    leftChild 9 PR SL normal579 4 7 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal579) 4 7 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal579) 4 7 114688).symm
    _ = cell593 := by rfl
theorem right296 : rightChild 9 PR SL normal579 4 7 114688 = cell594 := by
  calc
    rightChild 9 PR SL normal579 4 7 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal579) 4 7 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal579) 4 7 114688).symm
    _ = cell594 := by rfl
theorem normalized297 : AdaptiveCoverage.normalize SL cell593 = normal580 := by
  calc
    AdaptiveCoverage.normalize SL cell593 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell593)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell593)).symm
    _ = normal580 := by rfl
theorem left297 : leftChild 9 PR SL normal580 1 8 262144 = cell595 := by
  calc
    leftChild 9 PR SL normal580 1 8 262144 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal580) 1 8 262144).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal580) 1 8 262144).symm
    _ = cell595 := by rfl
theorem right297 : rightChild 9 PR SL normal580 1 8 262144 = cell596 := by
  calc
    rightChild 9 PR SL normal580 1 8 262144 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal580) 1 8 262144).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal580) 1 8 262144).symm
    _ = cell596 := by rfl
theorem normalized298 : AdaptiveCoverage.normalize SL cell595 = normal581 := by
  calc
    AdaptiveCoverage.normalize SL cell595 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell595)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell595)).symm
    _ = normal581 := by rfl
theorem left298 : leftChild 9 PR SL normal581 0 9 335872 = cell597 := by
  calc
    leftChild 9 PR SL normal581 0 9 335872 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal581) 0 9 335872).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal581) 0 9 335872).symm
    _ = cell597 := by rfl
theorem right298 : rightChild 9 PR SL normal581 0 9 335872 = cell598 := by
  calc
    rightChild 9 PR SL normal581 0 9 335872 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal581) 0 9 335872).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal581) 0 9 335872).symm
    _ = cell598 := by rfl
theorem normalized299 : AdaptiveCoverage.normalize SL cell572 = normal588 := by
  calc
    AdaptiveCoverage.normalize SL cell572 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell572)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell572)).symm
    _ = normal588 := by rfl
theorem left299 : leftChild 9 PR SL normal588 0 8 294912 = cell599 := by
  calc
    leftChild 9 PR SL normal588 0 8 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal588) 0 8 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal588) 0 8 294912).symm
    _ = cell599 := by rfl
theorem right299 : rightChild 9 PR SL normal588 0 8 294912 = cell600 := by
  calc
    rightChild 9 PR SL normal588 0 8 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal588) 0 8 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal588) 0 8 294912).symm
    _ = cell600 := by rfl
theorem normalized300 : AdaptiveCoverage.normalize SL cell599 = normal589 := by
  calc
    AdaptiveCoverage.normalize SL cell599 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell599)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell599)).symm
    _ = normal589 := by rfl
theorem left300 : leftChild 9 PR SL normal589 1 9 294912 = cell601 := by
  calc
    leftChild 9 PR SL normal589 1 9 294912 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal589) 1 9 294912).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal589) 1 9 294912).symm
    _ = cell601 := by rfl
theorem right300 : rightChild 9 PR SL normal589 1 9 294912 = cell602 := by
  calc
    rightChild 9 PR SL normal589 1 9 294912 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal589) 1 9 294912).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal589) 1 9 294912).symm
    _ = cell602 := by rfl
theorem normalized301 : AdaptiveCoverage.normalize SL cell601 = normal590 := by
  calc
    AdaptiveCoverage.normalize SL cell601 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell601)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell601)).symm
    _ = normal590 := by rfl
theorem left301 : leftChild 9 PR SL normal590 2 5 114688 = cell603 := by
  calc
    leftChild 9 PR SL normal590 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal590) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal590) 2 5 114688).symm
    _ = cell603 := by rfl
theorem right301 : rightChild 9 PR SL normal590 2 5 114688 = cell604 := by
  calc
    rightChild 9 PR SL normal590 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal590) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal590) 2 5 114688).symm
    _ = cell604 := by rfl
theorem normalized302 : AdaptiveCoverage.normalize SL cell602 = normal593 := by
  calc
    AdaptiveCoverage.normalize SL cell602 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell602)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell602)).symm
    _ = normal593 := by rfl
theorem left302 : leftChild 9 PR SL normal593 2 5 114688 = cell605 := by
  calc
    leftChild 9 PR SL normal593 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal593) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal593) 2 5 114688).symm
    _ = cell605 := by rfl
theorem right302 : rightChild 9 PR SL normal593 2 5 114688 = cell606 := by
  calc
    rightChild 9 PR SL normal593 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal593) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal593) 2 5 114688).symm
    _ = cell606 := by rfl
theorem normalized303 : AdaptiveCoverage.normalize SL cell605 = normal594 := by
  calc
    AdaptiveCoverage.normalize SL cell605 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell605)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell605)).symm
    _ = normal594 := by rfl
theorem left303 : leftChild 9 PR SL normal594 3 9 229376 = cell607 := by
  calc
    leftChild 9 PR SL normal594 3 9 229376 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal594) 3 9 229376).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal594) 3 9 229376).symm
    _ = cell607 := by rfl
theorem right303 : rightChild 9 PR SL normal594 3 9 229376 = cell608 := by
  calc
    rightChild 9 PR SL normal594 3 9 229376 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal594) 3 9 229376).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal594) 3 9 229376).symm
    _ = cell608 := by rfl

set_option pp.fullNames true
#print axioms normalized296
#print axioms left296
#print axioms right296
#print axioms normalized297
#print axioms left297
#print axioms right297
#print axioms normalized298
#print axioms left298
#print axioms right298
#print axioms normalized299
#print axioms left299
#print axioms right299
#print axioms normalized300
#print axioms left300
#print axioms right300
#print axioms normalized301
#print axioms left301
#print axioms right301
#print axioms normalized302
#print axioms left302
#print axioms right302
#print axioms normalized303
#print axioms left303
#print axioms right303
end StructuralGoal20261016.W10Aux478
end
