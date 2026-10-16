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
theorem normalized416 : AdaptiveCoverage.normalize SL cell760 = normal824 := by
  calc
    AdaptiveCoverage.normalize SL cell760 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell760)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell760)).symm
    _ = normal824 := by rfl
theorem left416 : leftChild 9 PR SL normal824 8 9 49195 = cell833 := by
  calc
    leftChild 9 PR SL normal824 8 9 49195 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal824) 8 9 49195).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal824) 8 9 49195).symm
    _ = cell833 := by rfl
theorem right416 : rightChild 9 PR SL normal824 8 9 49195 = cell834 := by
  calc
    rightChild 9 PR SL normal824 8 9 49195 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal824) 8 9 49195).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal824) 8 9 49195).symm
    _ = cell834 := by rfl
theorem normalized417 : AdaptiveCoverage.normalize SL cell833 = normal825 := by
  calc
    AdaptiveCoverage.normalize SL cell833 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell833)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell833)).symm
    _ = normal825 := by rfl
theorem left417 : leftChild 9 PR SL normal825 6 7 80690 = cell835 := by
  calc
    leftChild 9 PR SL normal825 6 7 80690 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal825) 6 7 80690).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal825) 6 7 80690).symm
    _ = cell835 := by rfl
theorem right417 : rightChild 9 PR SL normal825 6 7 80690 = cell836 := by
  calc
    rightChild 9 PR SL normal825 6 7 80690 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal825) 6 7 80690).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal825) 6 7 80690).symm
    _ = cell836 := by rfl
theorem normalized418 : AdaptiveCoverage.normalize SL cell835 = normal826 := by
  calc
    AdaptiveCoverage.normalize SL cell835 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell835)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell835)).symm
    _ = normal826 := by rfl
theorem left418 : leftChild 9 PR SL normal826 5 6 47741 = cell837 := by
  calc
    leftChild 9 PR SL normal826 5 6 47741 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal826) 5 6 47741).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal826) 5 6 47741).symm
    _ = cell837 := by rfl
theorem right418 : rightChild 9 PR SL normal826 5 6 47741 = cell838 := by
  calc
    rightChild 9 PR SL normal826 5 6 47741 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal826) 5 6 47741).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal826) 5 6 47741).symm
    _ = cell838 := by rfl
theorem normalized419 : AdaptiveCoverage.normalize SL cell837 = normal827 := by
  calc
    AdaptiveCoverage.normalize SL cell837 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell837)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell837)).symm
    _ = normal827 := by rfl
theorem left419 : leftChild 9 PR SL normal827 3 4 47725 = cell839 := by
  calc
    leftChild 9 PR SL normal827 3 4 47725 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal827) 3 4 47725).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal827) 3 4 47725).symm
    _ = cell839 := by rfl
theorem right419 : rightChild 9 PR SL normal827 3 4 47725 = cell840 := by
  calc
    rightChild 9 PR SL normal827 3 4 47725 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal827) 3 4 47725).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal827) 3 4 47725).symm
    _ = cell840 := by rfl
theorem normalized420 : AdaptiveCoverage.normalize SL cell839 = normal828 := by
  calc
    AdaptiveCoverage.normalize SL cell839 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell839)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell839)).symm
    _ = normal828 := by rfl
theorem left420 : leftChild 9 PR SL normal828 4 5 47629 = cell841 := by
  calc
    leftChild 9 PR SL normal828 4 5 47629 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal828) 4 5 47629).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal828) 4 5 47629).symm
    _ = cell841 := by rfl
theorem right420 : rightChild 9 PR SL normal828 4 5 47629 = cell842 := by
  calc
    rightChild 9 PR SL normal828 4 5 47629 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal828) 4 5 47629).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal828) 4 5 47629).symm
    _ = cell842 := by rfl
theorem normalized421 : AdaptiveCoverage.normalize SL cell841 = normal829 := by
  calc
    AdaptiveCoverage.normalize SL cell841 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell841)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell841)).symm
    _ = normal829 := by rfl
theorem left421 : leftChild 9 PR SL normal829 2 6 140288 = cell843 := by
  calc
    leftChild 9 PR SL normal829 2 6 140288 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal829) 2 6 140288).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal829) 2 6 140288).symm
    _ = cell843 := by rfl
theorem right421 : rightChild 9 PR SL normal829 2 6 140288 = cell844 := by
  calc
    rightChild 9 PR SL normal829 2 6 140288 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal829) 2 6 140288).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal829) 2 6 140288).symm
    _ = cell844 := by rfl
theorem normalized422 : AdaptiveCoverage.normalize SL cell843 = normal830 := by
  calc
    AdaptiveCoverage.normalize SL cell843 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell843)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell843)).symm
    _ = normal830 := by rfl
theorem left422 : leftChild 9 PR SL normal830 1 9 310271 = cell845 := by
  calc
    leftChild 9 PR SL normal830 1 9 310271 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal830) 1 9 310271).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal830) 1 9 310271).symm
    _ = cell845 := by rfl
theorem right422 : rightChild 9 PR SL normal830 1 9 310271 = cell846 := by
  calc
    rightChild 9 PR SL normal830 1 9 310271 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal830) 1 9 310271).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal830) 1 9 310271).symm
    _ = cell846 := by rfl
theorem normalized423 : AdaptiveCoverage.normalize SL cell844 = normal833 := by
  calc
    AdaptiveCoverage.normalize SL cell844 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell844)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell844)).symm
    _ = normal833 := by rfl
theorem left423 : leftChild 9 PR SL normal833 3 7 174016 = cell847 := by
  calc
    leftChild 9 PR SL normal833 3 7 174016 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal833) 3 7 174016).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal833) 3 7 174016).symm
    _ = cell847 := by rfl
theorem right423 : rightChild 9 PR SL normal833 3 7 174016 = cell848 := by
  calc
    rightChild 9 PR SL normal833 3 7 174016 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal833) 3 7 174016).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal833) 3 7 174016).symm
    _ = cell848 := by rfl

set_option pp.fullNames true
#print axioms normalized416
#print axioms left416
#print axioms right416
#print axioms normalized417
#print axioms left417
#print axioms right417
#print axioms normalized418
#print axioms left418
#print axioms right418
#print axioms normalized419
#print axioms left419
#print axioms right419
#print axioms normalized420
#print axioms left420
#print axioms right420
#print axioms normalized421
#print axioms left421
#print axioms right421
#print axioms normalized422
#print axioms left422
#print axioms right422
#print axioms normalized423
#print axioms left423
#print axioms right423
end StructuralGoal20261016.W10Aux478
end
