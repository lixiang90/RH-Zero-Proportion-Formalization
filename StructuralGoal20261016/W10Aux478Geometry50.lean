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
theorem normalized400 : AdaptiveCoverage.normalize SL cell800 = normal786 := by
  calc
    AdaptiveCoverage.normalize SL cell800 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell800)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell800)).symm
    _ = normal786 := by rfl
theorem left400 : leftChild 9 PR SL normal786 1 9 310815 = cell801 := by
  calc
    leftChild 9 PR SL normal786 1 9 310815 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal786) 1 9 310815).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal786) 1 9 310815).symm
    _ = cell801 := by rfl
theorem right400 : rightChild 9 PR SL normal786 1 9 310815 = cell802 := by
  calc
    rightChild 9 PR SL normal786 1 9 310815 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal786) 1 9 310815).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal786) 1 9 310815).symm
    _ = cell802 := by rfl
theorem normalized401 : AdaptiveCoverage.normalize SL cell798 = normal789 := by
  calc
    AdaptiveCoverage.normalize SL cell798 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell798)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell798)).symm
    _ = normal789 := by rfl
theorem left401 : leftChild 9 PR SL normal789 2 6 174270 = cell803 := by
  calc
    leftChild 9 PR SL normal789 2 6 174270 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal789) 2 6 174270).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal789) 2 6 174270).symm
    _ = cell803 := by rfl
theorem right401 : rightChild 9 PR SL normal789 2 6 174270 = cell804 := by
  calc
    rightChild 9 PR SL normal789 2 6 174270 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal789) 2 6 174270).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal789) 2 6 174270).symm
    _ = cell804 := by rfl
theorem normalized402 : AdaptiveCoverage.normalize SL cell804 = normal791 := by
  calc
    AdaptiveCoverage.normalize SL cell804 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell804)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell804)).symm
    _ = normal791 := by rfl
theorem left402 : leftChild 9 PR SL normal791 3 6 140095 = cell805 := by
  calc
    leftChild 9 PR SL normal791 3 6 140095 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal791) 3 6 140095).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal791) 3 6 140095).symm
    _ = cell805 := by rfl
theorem right402 : rightChild 9 PR SL normal791 3 6 140095 = cell806 := by
  calc
    rightChild 9 PR SL normal791 3 6 140095 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal791) 3 6 140095).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal791) 3 6 140095).symm
    _ = cell806 := by rfl
theorem normalized403 : AdaptiveCoverage.normalize SL cell792 = normal796 := by
  calc
    AdaptiveCoverage.normalize SL cell792 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell792)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell792)).symm
    _ = normal796 := by rfl
theorem left403 : leftChild 9 PR SL normal796 2 5 102704 = cell807 := by
  calc
    leftChild 9 PR SL normal796 2 5 102704 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal796) 2 5 102704).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal796) 2 5 102704).symm
    _ = cell807 := by rfl
theorem right403 : rightChild 9 PR SL normal796 2 5 102704 = cell808 := by
  calc
    rightChild 9 PR SL normal796 2 5 102704 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal796) 2 5 102704).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal796) 2 5 102704).symm
    _ = cell808 := by rfl
theorem normalized404 : AdaptiveCoverage.normalize SL cell808 = normal798 := by
  calc
    AdaptiveCoverage.normalize SL cell808 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell808)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell808)).symm
    _ = normal798 := by rfl
theorem left404 : leftChild 9 PR SL normal798 1 5 136640 = cell809 := by
  calc
    leftChild 9 PR SL normal798 1 5 136640 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal798) 1 5 136640).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal798) 1 5 136640).symm
    _ = cell809 := by rfl
theorem right404 : rightChild 9 PR SL normal798 1 5 136640 = cell810 := by
  calc
    rightChild 9 PR SL normal798 1 5 136640 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal798) 1 5 136640).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal798) 1 5 136640).symm
    _ = cell810 := by rfl
theorem normalized405 : AdaptiveCoverage.normalize SL cell762 = normal801 := by
  calc
    AdaptiveCoverage.normalize SL cell762 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell762)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell762)).symm
    _ = normal801 := by rfl
theorem left405 : leftChild 9 PR SL normal801 8 9 49163 = cell811 := by
  calc
    leftChild 9 PR SL normal801 8 9 49163 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal801) 8 9 49163).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal801) 8 9 49163).symm
    _ = cell811 := by rfl
theorem right405 : rightChild 9 PR SL normal801 8 9 49163 = cell812 := by
  calc
    rightChild 9 PR SL normal801 8 9 49163 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal801) 8 9 49163).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal801) 8 9 49163).symm
    _ = cell812 := by rfl
theorem normalized406 : AdaptiveCoverage.normalize SL cell811 = normal802 := by
  calc
    AdaptiveCoverage.normalize SL cell811 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell811)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell811)).symm
    _ = normal802 := by rfl
theorem left406 : leftChild 9 PR SL normal802 3 4 80140 = cell813 := by
  calc
    leftChild 9 PR SL normal802 3 4 80140 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal802) 3 4 80140).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal802) 3 4 80140).symm
    _ = cell813 := by rfl
theorem right406 : rightChild 9 PR SL normal802 3 4 80140 = cell814 := by
  calc
    rightChild 9 PR SL normal802 3 4 80140 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal802) 3 4 80140).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal802) 3 4 80140).symm
    _ = cell814 := by rfl
theorem normalized407 : AdaptiveCoverage.normalize SL cell813 = normal803 := by
  calc
    AdaptiveCoverage.normalize SL cell813 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell813)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell813)).symm
    _ = normal803 := by rfl
theorem left407 : leftChild 9 PR SL normal803 5 6 47725 = cell815 := by
  calc
    leftChild 9 PR SL normal803 5 6 47725 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal803) 5 6 47725).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal803) 5 6 47725).symm
    _ = cell815 := by rfl
theorem right407 : rightChild 9 PR SL normal803 5 6 47725 = cell816 := by
  calc
    rightChild 9 PR SL normal803 5 6 47725 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal803) 5 6 47725).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal803) 5 6 47725).symm
    _ = cell816 := by rfl

set_option pp.fullNames true
#print axioms normalized400
#print axioms left400
#print axioms right400
#print axioms normalized401
#print axioms left401
#print axioms right401
#print axioms normalized402
#print axioms left402
#print axioms right402
#print axioms normalized403
#print axioms left403
#print axioms right403
#print axioms normalized404
#print axioms left404
#print axioms right404
#print axioms normalized405
#print axioms left405
#print axioms right405
#print axioms normalized406
#print axioms left406
#print axioms right406
#print axioms normalized407
#print axioms left407
#print axioms right407
end StructuralGoal20261016.W10Aux478
end
