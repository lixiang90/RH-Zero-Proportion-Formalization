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
theorem normalized392 : AdaptiveCoverage.normalize SL cell784 = normal771 := by
  calc
    AdaptiveCoverage.normalize SL cell784 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell784)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell784)).symm
    _ = normal771 := by rfl
theorem left392 : leftChild 9 PR SL normal771 3 6 139600 = cell785 := by
  calc
    leftChild 9 PR SL normal771 3 6 139600 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal771) 3 6 139600).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal771) 3 6 139600).symm
    _ = cell785 := by rfl
theorem right392 : rightChild 9 PR SL normal771 3 6 139600 = cell786 := by
  calc
    rightChild 9 PR SL normal771 3 6 139600 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal771) 3 6 139600).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal771) 3 6 139600).symm
    _ = cell786 := by rfl
theorem normalized393 : AdaptiveCoverage.normalize SL cell774 = normal775 := by
  calc
    AdaptiveCoverage.normalize SL cell774 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell774)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell774)).symm
    _ = normal775 := by rfl
theorem left393 : leftChild 9 PR SL normal775 3 8 201424 = cell787 := by
  calc
    leftChild 9 PR SL normal775 3 8 201424 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal775) 3 8 201424).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal775) 3 8 201424).symm
    _ = cell787 := by rfl
theorem right393 : rightChild 9 PR SL normal775 3 8 201424 = cell788 := by
  calc
    rightChild 9 PR SL normal775 3 8 201424 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal775) 3 8 201424).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal775) 3 8 201424).symm
    _ = cell788 := by rfl
theorem normalized394 : AdaptiveCoverage.normalize SL cell788 = normal777 := by
  calc
    AdaptiveCoverage.normalize SL cell788 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell788)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell788)).symm
    _ = normal777 := by rfl
theorem left394 : leftChild 9 PR SL normal777 3 8 214592 = cell789 := by
  calc
    leftChild 9 PR SL normal777 3 8 214592 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal777) 3 8 214592).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal777) 3 8 214592).symm
    _ = cell789 := by rfl
theorem right394 : rightChild 9 PR SL normal777 3 8 214592 = cell790 := by
  calc
    rightChild 9 PR SL normal777 3 8 214592 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal777) 3 8 214592).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal777) 3 8 214592).symm
    _ = cell790 := by rfl
theorem normalized395 : AdaptiveCoverage.normalize SL cell764 = normal780 := by
  calc
    AdaptiveCoverage.normalize SL cell764 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell764)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell764)).symm
    _ = normal780 := by rfl
theorem left395 : leftChild 9 PR SL normal780 8 9 49147 = cell791 := by
  calc
    leftChild 9 PR SL normal780 8 9 49147 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal780) 8 9 49147).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal780) 8 9 49147).symm
    _ = cell791 := by rfl
theorem right395 : rightChild 9 PR SL normal780 8 9 49147 = cell792 := by
  calc
    rightChild 9 PR SL normal780 8 9 49147 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal780) 8 9 49147).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal780) 8 9 49147).symm
    _ = cell792 := by rfl
theorem normalized396 : AdaptiveCoverage.normalize SL cell791 = normal781 := by
  calc
    AdaptiveCoverage.normalize SL cell791 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell791)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell791)).symm
    _ = normal781 := by rfl
theorem left396 : leftChild 9 PR SL normal781 5 6 80140 = cell793 := by
  calc
    leftChild 9 PR SL normal781 5 6 80140 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal781) 5 6 80140).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal781) 5 6 80140).symm
    _ = cell793 := by rfl
theorem right396 : rightChild 9 PR SL normal781 5 6 80140 = cell794 := by
  calc
    rightChild 9 PR SL normal781 5 6 80140 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal781) 5 6 80140).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal781) 5 6 80140).symm
    _ = cell794 := by rfl
theorem normalized397 : AdaptiveCoverage.normalize SL cell793 = normal782 := by
  calc
    AdaptiveCoverage.normalize SL cell793 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell793)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell793)).symm
    _ = normal782 := by rfl
theorem left397 : leftChild 9 PR SL normal782 4 5 47629 = cell795 := by
  calc
    leftChild 9 PR SL normal782 4 5 47629 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal782) 4 5 47629).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal782) 4 5 47629).symm
    _ = cell795 := by rfl
theorem right397 : rightChild 9 PR SL normal782 4 5 47629 = cell796 := by
  calc
    rightChild 9 PR SL normal782 4 5 47629 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal782) 4 5 47629).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal782) 4 5 47629).symm
    _ = cell796 := by rfl
theorem normalized398 : AdaptiveCoverage.normalize SL cell795 = normal783 := by
  calc
    AdaptiveCoverage.normalize SL cell795 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell795)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell795)).symm
    _ = normal783 := by rfl
theorem left398 : leftChild 9 PR SL normal783 3 7 173296 = cell797 := by
  calc
    leftChild 9 PR SL normal783 3 7 173296 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal783) 3 7 173296).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal783) 3 7 173296).symm
    _ = cell797 := by rfl
theorem right398 : rightChild 9 PR SL normal783 3 7 173296 = cell798 := by
  calc
    rightChild 9 PR SL normal783 3 7 173296 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal783) 3 7 173296).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal783) 3 7 173296).symm
    _ = cell798 := by rfl
theorem normalized399 : AdaptiveCoverage.normalize SL cell797 = normal784 := by
  calc
    AdaptiveCoverage.normalize SL cell797 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell797)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell797)).symm
    _ = normal784 := by rfl
theorem left399 : leftChild 9 PR SL normal784 0 8 309819 = cell799 := by
  calc
    leftChild 9 PR SL normal784 0 8 309819 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal784) 0 8 309819).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal784) 0 8 309819).symm
    _ = cell799 := by rfl
theorem right399 : rightChild 9 PR SL normal784 0 8 309819 = cell800 := by
  calc
    rightChild 9 PR SL normal784 0 8 309819 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal784) 0 8 309819).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal784) 0 8 309819).symm
    _ = cell800 := by rfl

set_option pp.fullNames true
#print axioms normalized392
#print axioms left392
#print axioms right392
#print axioms normalized393
#print axioms left393
#print axioms right393
#print axioms normalized394
#print axioms left394
#print axioms right394
#print axioms normalized395
#print axioms left395
#print axioms right395
#print axioms normalized396
#print axioms left396
#print axioms right396
#print axioms normalized397
#print axioms left397
#print axioms right397
#print axioms normalized398
#print axioms left398
#print axioms right398
#print axioms normalized399
#print axioms left399
#print axioms right399
end StructuralGoal20261016.W10Aux478
end
