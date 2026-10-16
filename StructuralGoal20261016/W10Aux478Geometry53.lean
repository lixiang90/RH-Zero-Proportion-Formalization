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
theorem normalized424 : AdaptiveCoverage.normalize SL cell836 = normal839 := by
  calc
    AdaptiveCoverage.normalize SL cell836 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell836)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell836)).symm
    _ = normal839 := by rfl
theorem left424 : leftChild 9 PR SL normal839 2 6 137664 = cell849 := by
  calc
    leftChild 9 PR SL normal839 2 6 137664 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal839) 2 6 137664).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal839) 2 6 137664).symm
    _ = cell849 := by rfl
theorem right424 : rightChild 9 PR SL normal839 2 6 137664 = cell850 := by
  calc
    rightChild 9 PR SL normal839 2 6 137664 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal839) 2 6 137664).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal839) 2 6 137664).symm
    _ = cell850 := by rfl
theorem normalized425 : AdaptiveCoverage.normalize SL cell834 = normal842 := by
  calc
    AdaptiveCoverage.normalize SL cell834 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell834)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell834)).symm
    _ = normal842 := by rfl
theorem left425 : leftChild 9 PR SL normal842 2 6 137088 = cell851 := by
  calc
    leftChild 9 PR SL normal842 2 6 137088 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal842) 2 6 137088).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal842) 2 6 137088).symm
    _ = cell851 := by rfl
theorem right425 : rightChild 9 PR SL normal842 2 6 137088 = cell852 := by
  calc
    rightChild 9 PR SL normal842 2 6 137088 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal842) 2 6 137088).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal842) 2 6 137088).symm
    _ = cell852 := by rfl
theorem normalized426 : AdaptiveCoverage.normalize SL cell852 = normal844 := by
  calc
    AdaptiveCoverage.normalize SL cell852 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell852)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell852)).symm
    _ = normal844 := by rfl
theorem left426 : leftChild 9 PR SL normal844 0 6 204288 = cell853 := by
  calc
    leftChild 9 PR SL normal844 0 6 204288 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal844) 0 6 204288).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal844) 0 6 204288).symm
    _ = cell853 := by rfl
theorem right426 : rightChild 9 PR SL normal844 0 6 204288 = cell854 := by
  calc
    rightChild 9 PR SL normal844 0 6 204288 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal844) 0 6 204288).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal844) 0 6 204288).symm
    _ = cell854 := by rfl
theorem normalized427 : AdaptiveCoverage.normalize SL cell758 = normal847 := by
  calc
    AdaptiveCoverage.normalize SL cell758 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell758)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell758)).symm
    _ = normal847 := by rfl
theorem left427 : leftChild 9 PR SL normal847 8 9 49195 = cell855 := by
  calc
    leftChild 9 PR SL normal847 8 9 49195 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal847) 8 9 49195).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal847) 8 9 49195).symm
    _ = cell855 := by rfl
theorem right427 : rightChild 9 PR SL normal847 8 9 49195 = cell856 := by
  calc
    rightChild 9 PR SL normal847 8 9 49195 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal847) 8 9 49195).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal847) 8 9 49195).symm
    _ = cell856 := by rfl
theorem normalized428 : AdaptiveCoverage.normalize SL cell855 = normal848 := by
  calc
    AdaptiveCoverage.normalize SL cell855 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell855)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell855)).symm
    _ = normal848 := by rfl
theorem left428 : leftChild 9 PR SL normal848 2 3 80690 = cell857 := by
  calc
    leftChild 9 PR SL normal848 2 3 80690 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal848) 2 3 80690).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal848) 2 3 80690).symm
    _ = cell857 := by rfl
theorem right428 : rightChild 9 PR SL normal848 2 3 80690 = cell858 := by
  calc
    rightChild 9 PR SL normal848 2 3 80690 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal848) 2 3 80690).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal848) 2 3 80690).symm
    _ = cell858 := by rfl
theorem normalized429 : AdaptiveCoverage.normalize SL cell857 = normal849 := by
  calc
    AdaptiveCoverage.normalize SL cell857 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell857)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell857)).symm
    _ = normal849 := by rfl
theorem left429 : leftChild 9 PR SL normal849 6 7 48274 = cell859 := by
  calc
    leftChild 9 PR SL normal849 6 7 48274 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal849) 6 7 48274).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal849) 6 7 48274).symm
    _ = cell859 := by rfl
theorem right429 : rightChild 9 PR SL normal849 6 7 48274 = cell860 := by
  calc
    rightChild 9 PR SL normal849 6 7 48274 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal849) 6 7 48274).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal849) 6 7 48274).symm
    _ = cell860 := by rfl
theorem normalized430 : AdaptiveCoverage.normalize SL cell859 = normal850 := by
  calc
    AdaptiveCoverage.normalize SL cell859 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell859)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell859)).symm
    _ = normal850 := by rfl
theorem left430 : leftChild 9 PR SL normal850 3 4 47741 = cell861 := by
  calc
    leftChild 9 PR SL normal850 3 4 47741 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal850) 3 4 47741).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal850) 3 4 47741).symm
    _ = cell861 := by rfl
theorem right430 : rightChild 9 PR SL normal850 3 4 47741 = cell862 := by
  calc
    rightChild 9 PR SL normal850 3 4 47741 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal850) 3 4 47741).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal850) 3 4 47741).symm
    _ = cell862 := by rfl
theorem normalized431 : AdaptiveCoverage.normalize SL cell861 = normal851 := by
  calc
    AdaptiveCoverage.normalize SL cell861 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell861)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell861)).symm
    _ = normal851 := by rfl
theorem left431 : leftChild 9 PR SL normal851 5 6 47741 = cell863 := by
  calc
    leftChild 9 PR SL normal851 5 6 47741 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal851) 5 6 47741).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal851) 5 6 47741).symm
    _ = cell863 := by rfl
theorem right431 : rightChild 9 PR SL normal851 5 6 47741 = cell864 := by
  calc
    rightChild 9 PR SL normal851 5 6 47741 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal851) 5 6 47741).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal851) 5 6 47741).symm
    _ = cell864 := by rfl

set_option pp.fullNames true
#print axioms normalized424
#print axioms left424
#print axioms right424
#print axioms normalized425
#print axioms left425
#print axioms right425
#print axioms normalized426
#print axioms left426
#print axioms right426
#print axioms normalized427
#print axioms left427
#print axioms right427
#print axioms normalized428
#print axioms left428
#print axioms right428
#print axioms normalized429
#print axioms left429
#print axioms right429
#print axioms normalized430
#print axioms left430
#print axioms right430
#print axioms normalized431
#print axioms left431
#print axioms right431
end StructuralGoal20261016.W10Aux478
end
