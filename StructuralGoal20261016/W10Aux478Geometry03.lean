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
theorem normalized024 : AdaptiveCoverage.normalize SL cell047 = normal041 := by
  calc
    AdaptiveCoverage.normalize SL cell047 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell047)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell047)).symm
    _ = normal041 := by rfl
theorem left024 : leftChild 9 PR SL normal041 1 9 311296 = cell049 := by
  calc
    leftChild 9 PR SL normal041 1 9 311296 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal041) 1 9 311296).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal041) 1 9 311296).symm
    _ = cell049 := by rfl
theorem right024 : rightChild 9 PR SL normal041 1 9 311296 = cell050 := by
  calc
    rightChild 9 PR SL normal041 1 9 311296 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal041) 1 9 311296).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal041) 1 9 311296).symm
    _ = cell050 := by rfl
theorem normalized025 : AdaptiveCoverage.normalize SL cell050 = normal043 := by
  calc
    AdaptiveCoverage.normalize SL cell050 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell050)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell050)).symm
    _ = normal043 := by rfl
theorem left025 : leftChild 9 PR SL normal043 3 9 245760 = cell051 := by
  calc
    leftChild 9 PR SL normal043 3 9 245760 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal043) 3 9 245760).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal043) 3 9 245760).symm
    _ = cell051 := by rfl
theorem right025 : rightChild 9 PR SL normal043 3 9 245760 = cell052 := by
  calc
    rightChild 9 PR SL normal043 3 9 245760 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal043) 3 9 245760).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal043) 3 9 245760).symm
    _ = cell052 := by rfl
theorem normalized026 : AdaptiveCoverage.normalize SL cell052 = normal045 := by
  calc
    AdaptiveCoverage.normalize SL cell052 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell052)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell052)).symm
    _ = normal045 := by rfl
theorem left026 : leftChild 9 PR SL normal045 2 5 114688 = cell053 := by
  calc
    leftChild 9 PR SL normal045 2 5 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal045) 2 5 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal045) 2 5 114688).symm
    _ = cell053 := by rfl
theorem right026 : rightChild 9 PR SL normal045 2 5 114688 = cell054 := by
  calc
    rightChild 9 PR SL normal045 2 5 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal045) 2 5 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal045) 2 5 114688).symm
    _ = cell054 := by rfl
theorem normalized027 : AdaptiveCoverage.normalize SL cell053 = normal046 := by
  calc
    AdaptiveCoverage.normalize SL cell053 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell053)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell053)).symm
    _ = normal046 := by rfl
theorem left027 : leftChild 9 PR SL normal046 4 7 114688 = cell055 := by
  calc
    leftChild 9 PR SL normal046 4 7 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal046) 4 7 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal046) 4 7 114688).symm
    _ = cell055 := by rfl
theorem right027 : rightChild 9 PR SL normal046 4 7 114688 = cell056 := by
  calc
    rightChild 9 PR SL normal046 4 7 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal046) 4 7 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal046) 4 7 114688).symm
    _ = cell056 := by rfl
theorem normalized028 : AdaptiveCoverage.normalize SL cell055 = normal047 := by
  calc
    AdaptiveCoverage.normalize SL cell055 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell055)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell055)).symm
    _ = normal047 := by rfl
theorem left028 : leftChild 9 PR SL normal047 3 6 114688 = cell057 := by
  calc
    leftChild 9 PR SL normal047 3 6 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal047) 3 6 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal047) 3 6 114688).symm
    _ = cell057 := by rfl
theorem right028 : rightChild 9 PR SL normal047 3 6 114688 = cell058 := by
  calc
    rightChild 9 PR SL normal047 3 6 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal047) 3 6 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal047) 3 6 114688).symm
    _ = cell058 := by rfl
theorem normalized029 : AdaptiveCoverage.normalize SL cell057 = normal048 := by
  calc
    AdaptiveCoverage.normalize SL cell057 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell057)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell057)).symm
    _ = normal048 := by rfl
theorem left029 : leftChild 9 PR SL normal048 0 8 262144 = cell059 := by
  calc
    leftChild 9 PR SL normal048 0 8 262144 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal048) 0 8 262144).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal048) 0 8 262144).symm
    _ = cell059 := by rfl
theorem right029 : rightChild 9 PR SL normal048 0 8 262144 = cell060 := by
  calc
    rightChild 9 PR SL normal048 0 8 262144 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal048) 0 8 262144).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal048) 0 8 262144).symm
    _ = cell060 := by rfl
theorem normalized030 : AdaptiveCoverage.normalize SL cell060 = normal050 := by
  calc
    AdaptiveCoverage.normalize SL cell060 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell060)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell060)).symm
    _ = normal050 := by rfl
theorem left030 : leftChild 9 PR SL normal050 0 9 352256 = cell061 := by
  calc
    leftChild 9 PR SL normal050 0 9 352256 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal050) 0 9 352256).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal050) 0 9 352256).symm
    _ = cell061 := by rfl
theorem right030 : rightChild 9 PR SL normal050 0 9 352256 = cell062 := by
  calc
    rightChild 9 PR SL normal050 0 9 352256 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal050) 0 9 352256).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal050) 0 9 352256).symm
    _ = cell062 := by rfl
theorem normalized031 : AdaptiveCoverage.normalize SL cell062 = normal052 := by
  calc
    AdaptiveCoverage.normalize SL cell062 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell062)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell062)).symm
    _ = normal052 := by rfl
theorem left031 : leftChild 9 PR SL normal052 2 6 147456 = cell063 := by
  calc
    leftChild 9 PR SL normal052 2 6 147456 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal052) 2 6 147456).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal052) 2 6 147456).symm
    _ = cell063 := by rfl
theorem right031 : rightChild 9 PR SL normal052 2 6 147456 = cell064 := by
  calc
    rightChild 9 PR SL normal052 2 6 147456 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal052) 2 6 147456).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal052) 2 6 147456).symm
    _ = cell064 := by rfl

set_option pp.fullNames true
#print axioms normalized024
#print axioms left024
#print axioms right024
#print axioms normalized025
#print axioms left025
#print axioms right025
#print axioms normalized026
#print axioms left026
#print axioms right026
#print axioms normalized027
#print axioms left027
#print axioms right027
#print axioms normalized028
#print axioms left028
#print axioms right028
#print axioms normalized029
#print axioms left029
#print axioms right029
#print axioms normalized030
#print axioms left030
#print axioms right030
#print axioms normalized031
#print axioms left031
#print axioms right031
end StructuralGoal20261016.W10Aux478
end
