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
theorem normalized456 : AdaptiveCoverage.normalize SL cell754 = normal907 := by
  calc
    AdaptiveCoverage.normalize SL cell754 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell754)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell754)).symm
    _ = normal907 := by rfl
theorem left456 : leftChild 9 PR SL normal907 8 9 49127 = cell913 := by
  calc
    leftChild 9 PR SL normal907 8 9 49127 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal907) 8 9 49127).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal907) 8 9 49127).symm
    _ = cell913 := by rfl
theorem right456 : rightChild 9 PR SL normal907 8 9 49127 = cell914 := by
  calc
    rightChild 9 PR SL normal907 8 9 49127 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal907) 8 9 49127).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal907) 8 9 49127).symm
    _ = cell914 := by rfl
theorem normalized457 : AdaptiveCoverage.normalize SL cell913 = normal908 := by
  calc
    AdaptiveCoverage.normalize SL cell913 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell913)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell913)).symm
    _ = normal908 := by rfl
theorem left457 : leftChild 9 PR SL normal908 7 8 81036 = cell915 := by
  calc
    leftChild 9 PR SL normal908 7 8 81036 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal908) 7 8 81036).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal908) 7 8 81036).symm
    _ = cell915 := by rfl
theorem right457 : rightChild 9 PR SL normal908 7 8 81036 = cell916 := by
  calc
    rightChild 9 PR SL normal908 7 8 81036 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal908) 7 8 81036).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal908) 7 8 81036).symm
    _ = cell916 := by rfl
theorem normalized458 : AdaptiveCoverage.normalize SL cell915 = normal909 := by
  calc
    AdaptiveCoverage.normalize SL cell915 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell915)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell915)).symm
    _ = normal909 := by rfl
theorem left458 : leftChild 9 PR SL normal909 1 2 48668 = cell917 := by
  calc
    leftChild 9 PR SL normal909 1 2 48668 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal909) 1 2 48668).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal909) 1 2 48668).symm
    _ = cell917 := by rfl
theorem right458 : rightChild 9 PR SL normal909 1 2 48668 = cell918 := by
  calc
    rightChild 9 PR SL normal909 1 2 48668 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal909) 1 2 48668).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal909) 1 2 48668).symm
    _ = cell918 := by rfl
theorem normalized459 : AdaptiveCoverage.normalize SL cell917 = normal910 := by
  calc
    AdaptiveCoverage.normalize SL cell917 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell917)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell917)).symm
    _ = normal910 := by rfl
theorem left459 : leftChild 9 PR SL normal910 6 7 48247 = cell919 := by
  calc
    leftChild 9 PR SL normal910 6 7 48247 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal910) 6 7 48247).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal910) 6 7 48247).symm
    _ = cell919 := by rfl
theorem right459 : rightChild 9 PR SL normal910 6 7 48247 = cell920 := by
  calc
    rightChild 9 PR SL normal910 6 7 48247 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal910) 6 7 48247).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal910) 6 7 48247).symm
    _ = cell920 := by rfl
theorem normalized460 : AdaptiveCoverage.normalize SL cell919 = normal911 := by
  calc
    AdaptiveCoverage.normalize SL cell919 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell919)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell919)).symm
    _ = normal911 := by rfl
theorem left460 : leftChild 9 PR SL normal911 2 3 48247 = cell921 := by
  calc
    leftChild 9 PR SL normal911 2 3 48247 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal911) 2 3 48247).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal911) 2 3 48247).symm
    _ = cell921 := by rfl
theorem right460 : rightChild 9 PR SL normal911 2 3 48247 = cell922 := by
  calc
    rightChild 9 PR SL normal911 2 3 48247 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal911) 2 3 48247).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal911) 2 3 48247).symm
    _ = cell922 := by rfl
theorem normalized461 : AdaptiveCoverage.normalize SL cell921 = normal912 := by
  calc
    AdaptiveCoverage.normalize SL cell921 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell921)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell921)).symm
    _ = normal912 := by rfl
theorem left461 : leftChild 9 PR SL normal912 3 4 47724 = cell923 := by
  calc
    leftChild 9 PR SL normal912 3 4 47724 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal912) 3 4 47724).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal912) 3 4 47724).symm
    _ = cell923 := by rfl
theorem right461 : rightChild 9 PR SL normal912 3 4 47724 = cell924 := by
  calc
    rightChild 9 PR SL normal912 3 4 47724 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal912) 3 4 47724).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal912) 3 4 47724).symm
    _ = cell924 := by rfl
theorem normalized462 : AdaptiveCoverage.normalize SL cell923 = normal913 := by
  calc
    AdaptiveCoverage.normalize SL cell923 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell923)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell923)).symm
    _ = normal913 := by rfl
theorem left462 : leftChild 9 PR SL normal913 5 6 47724 = cell925 := by
  calc
    leftChild 9 PR SL normal913 5 6 47724 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal913) 5 6 47724).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal913) 5 6 47724).symm
    _ = cell925 := by rfl
theorem right462 : rightChild 9 PR SL normal913 5 6 47724 = cell926 := by
  calc
    rightChild 9 PR SL normal913 5 6 47724 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal913) 5 6 47724).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal913) 5 6 47724).symm
    _ = cell926 := by rfl
theorem normalized463 : AdaptiveCoverage.normalize SL cell925 = normal914 := by
  calc
    AdaptiveCoverage.normalize SL cell925 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell925)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell925)).symm
    _ = normal914 := by rfl
theorem left463 : leftChild 9 PR SL normal914 4 5 47532 = cell927 := by
  calc
    leftChild 9 PR SL normal914 4 5 47532 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal914) 4 5 47532).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal914) 4 5 47532).symm
    _ = cell927 := by rfl
theorem right463 : rightChild 9 PR SL normal914 4 5 47532 = cell928 := by
  calc
    rightChild 9 PR SL normal914 4 5 47532 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal914) 4 5 47532).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal914) 4 5 47532).symm
    _ = cell928 := by rfl

set_option pp.fullNames true
#print axioms normalized456
#print axioms left456
#print axioms right456
#print axioms normalized457
#print axioms left457
#print axioms right457
#print axioms normalized458
#print axioms left458
#print axioms right458
#print axioms normalized459
#print axioms left459
#print axioms right459
#print axioms normalized460
#print axioms left460
#print axioms right460
#print axioms normalized461
#print axioms left461
#print axioms right461
#print axioms normalized462
#print axioms left462
#print axioms right462
#print axioms normalized463
#print axioms left463
#print axioms right463
end StructuralGoal20261016.W10Aux478
end
